"use strict";
(function(){

var enc = new TextEncoder(), dec = new TextDecoder(); // utf-8

function kw(caps) { // "THEN" => U8[84,116, 72,104, 69,101, 78,110]
  var i, b = enc.encode(caps), v = new Uint8Array(b.length*2), p=0;
  for (i=0; i<b.length; i++) { v[p++] = b[i]; v[p++] = b[i]+32; } // +32 to lower-case.
  return v;
}

var REM=kw("REM"),LET=kw("LET"),DIM=kw("DIM"),THEN=kw("THEN"),ELSE=kw("ELSE"),FOR=kw("FOR"),NEXT=kw("NEXT");
var REPEAT=kw("REPEAT"),WHILE=kw("WHILE"),CASE=kw("CASE"),END=kw("END"),GOTO=kw("GOTO"),TAB=kw("TAB");
var GOSUB=kw("GOSUB"),RETURN=kw("RETURN"),READ=kw("READ"),RESTORE=kw("RESTORE"),SET=kw("SET");
var PRINT=kw("PRINT"),PROC=kw("PROC"),AND=kw("AND"),OR=kw("OR"),EOR=kw("EOR"),NOT=kw("NOT");
var n_funs = [
  'GET','INKEY','RND','TIME','DIM',
  'FLOOR','CEIL','ABS','ATN','COS','EXP','INT','SGN','SIN','SQR','LOG','LN','TAN','PI',
  'LEN','INSTR','ASC','VAL'
];
var s_funs = [ // fns ending with '$'
  'GET','INKEY','LEFT','MID','RIGHT','STRING','CHR','STR','BIN','HEX','TAT','UC','LC'
];

function log(c,p,msg) {
  console.log(`${msg} ${subs(c,p-4,p+5)}\n${'^'.padStart(msg.length+6)}`);
}

function isAlpha(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95 || c === 64; } // [A-Za-z_@]
function rest(c,p) { return dec.decode(c.slice(p)); }
function subs(c,s,e) { return dec.decode(c.slice(s,e)); }
function skip_ws(c,p) { while (c[p] === 32) ++p; return p; }

function m_error(c,p,msg) {
  var at = skip_ws(c,p);
  while (p<c.length && c[p]!==58) ++p; // up to ":"
  return { $:'error', at, msg, text:subs(c,at,p), aft:p };
}

function m_stmts(c,p,req,stmts) {
  var s;
  for (;;) {
    s = m_stmt(c,p,req);
    if (!s) break;
    stmts.push(s);
    p = skip_ws(c,s.aft);
    if (c[p] === 58) { ++p; req=':'; continue; } // ":"
    else break;
  }
  return p;
}

function m_stmt(c,p,req) {
  p = skip_ws(c,p);
  var t, s, at=p;
  switch (c[p]) {
    case 63: { // "?" shorthand PRINT.
      return m_print(c,p,at);
    }
    case 68: case 100: {  // "D"
      t = is_kw(c,p,DIM,3);
      if (t) return m_dim(c,t,at);
      break;
    }
    case 70: case 102: { // "F"
      break;
    }
    case 71: case 103: { // "G"
      t = is_kw(c,p,GOTO,1);
      if (t) return m_goto_line(c,t,"Expecting a line number after GOTO");
      t = is_kw(c,p,GOSUB,3);
      if (t) return m_goto_line(c,t,"Expecting a line number after GOTO");
      break;
    }
    case 73: case 105: { t = c[p+1]; // "I"
      if (t === 70 || t === 102) {   // "F"
        return m_if(c,p+2,at);
      }
      break;
    }
    case 76: case 108: { // "L"
      t = is_kw(c,p,LET,3);
      if (t) return m_let(c,t,at,0);
      break;
    }
    case 80: case 112: { // "P"
      t = is_kw(c,p,PRINT,1);
      if (t) return m_print(c,t,at);
      t = is_kw(c,p,PROC,4);
      if (t) return m_fn_proc(c,t,at,'proc');
      break;
    }
    case 82: case 114: { // "R"
      t = is_kw(c,p,REM,3);
      if (t) return m_rem(c,t,at);
      t = is_kw(c,p,RETURN,1);
      if (t) return { $:'return', at, aft:t }
      break;
    }
  }
  s = m_let(c,p,at,1); if (s) return s;
  if (!req) return null; // no match.
  return m_error(c,at,'Unrecognised Statement after '+req+' (Statement expected)')
}

function m_rem(c,p,at) {
  p = skip_ws(c,p);
  return { $:'rem', at, text:subs(c,p,c.length), aft:c.length }
}

function m_let(c,p,at,opt) {
  var name, exp=null, err=null;
  p = skip_ws(c,p);
  name = m_ident_i(c,p,1,1);
  if (name) {
    p = skip_ws(c,name.aft);
    if (c[p] === 61) { // "="
      exp = m_expr(c,p+1,0,0); p=exp.aft;
    } else {
      if (opt) return null; // not a LET stmt!
      err = m_error(c,p,"Missing = in Let statement"); p=err.aft;
    }
  } else {
    if (opt) return null;
    err = m_error(c,p,"Missing name in Let statement"); p=err.aft;
  }
  return { $:'let', at, name, exp, err, aft:p }
}

function m_dim(c,p,at) {
  var dims=[], err=null, name, args, a0, a1;
  for (;;) {
    p = skip_ws(c,p); a0=p;
    name = m_ident_i(c,p,0,1); args=[];
    p = skip_ws(c,name.aft);
    if (c[p] === 40) { a1=p; // "("
      p = m_args(c, p+1, args);
      if (c[p] === 41) ++p; // ")"
      else { err = m_error(c,p,"Missing ) to end Dim (opened at "+(a1+1)+")"); p=err.aft; }
    } else { err = m_error(c,p,"Missing ( after name in Dim"); p=err.aft; }
    dims.push({ at:a0, name, args });
    if (!err && c[p] === 44) { ++p; continue; } // ","
    else break;
  }
  return { $:'dim', at, dims, err, aft:p }
}

// input: prints a "?"

function m_print(c,p,at) {
  var t, s, vals=[], sem, ts=0;
  // prefix ";" prevents leading right-align for a number (comma for column)
  // TAB(c) advance to column c, next line if necessary
  for (;;) {
    p = skip_ws(c,p); sem=0;
    switch (c[p]) {
      case 59: sem=1; ++p; break; // ";" semis join without gaps
      case 44: sem=2; ++p; break; // "," commas create fields
      case 39: sem=3; ++p; break; // "'" begin new line
    }
    // can be a TAB() clause.
    if (sem) p = skip_ws(c,p) ;; t=c[p];
    if (t === 84 || t === 116) { // "T"
      s = m_tab(c,p,sem);
      if (s) { vals.push(sem, exp); p=s.aft; continue; }
    }
    // expr or end of print.
    var exp = m_expr(c,p,1,0)
    if (exp !== null) {
      vals.push(sem, exp); p = exp.aft;
    } else {
      p = skip_ws(c,p);
      if (c[p] === 59) { ts=1; ++p; } // trailing ";"
      return { $:'print', at, vals, ts, aft:p }
    }
  }
}

function m_tab(c,p,sem) {
  var x, y, t = is_kw(c,p,TAB,3), err=null, at=p;
  if (t && c[p+3] === 40) { // "TAB("
    x = m_expr(c,p+4,0,0); p=skip_ws(c,x.aft);
    if (c[p] === 44) { // ","
      y = m_expr(c,p+1,0,0); p=skip_ws(c,y.aft);
    }
    if (c[p] !== 41) { // ")"
      err = m_error(c,p,"Missing ) to end TAB()"); p=err.aft;
    }
    return { pm:'tab', at, sem, x, y, err, aft:p }
  }
}

function m_if(c,p,at) {
  // IF•{expr}[THEN]{ln/stmt}[ELSE{ln/stmt}]
  var cond, then_s=[], else_s=[], thn, els, err=null;
  cond = m_expr(c,p,1,0);
  if (cond === null) {
    err = m_error(c,p,"Incomplete IF statement (Condition expected)"); p=err.aft;
  } else {
    thn = is_kw(c, cond.aft, THEN, 2);
    if (thn) {
      p = m_stmts_goto(c, thn, 'THEN', then_s);
    } else { // missing THEN, Stmts allowed.
      p = m_stmts(c, cond.aft, '', then_s);
    }
    if (then_s.length) { // has THEN/Stmts?
      els = is_kw(c, p, ELSE, 2);
      if (els) p = m_stmts_goto(c, els, 'ELSE', else_s);
    } else { // parse as LET•IFN= instead of IF-Stmt.
      // TODO.
      err = m_error(c,p,"Missing THEN after IF condition (Statement expected)"); p=err.aft;
    }
  }
  return { $:'if', at, cond, then_s, else_s, err, aft:p }
}

function m_stmts_goto(c,p,req,stmts) {
  var s = m_goto_line(c,p,null);
  if (s !== null) { stmts.push(s); return s.aft; }
  return m_stmts(c,p,req,stmts);
}

function m_goto_line(c,p,req) {
  p = skip_ws(c,p);
  var num = m_number_i(c,p,req);
  if (num) {
    // Implicit GoTo (a line number)
    return { $:'goto', at:num.at, line:num.val, aft:num.aft }
  }
  return null;
}

function m_ident_i(c,p,opt,suf) {
  var at=p, t=c[p], typ='', e;
  while (isAlpha(t)) t=c[++p];
  if (p > at) { e=p;
    if (suf) {
      if (t === 37) { ++p; typ='%' } // "%"
      else if (t === 36) { ++p; typ='$' } // "$"
    }
    return { $:'name', at, name:subs(c,at,e), typ, aft:p }
  }
  if (opt) return null; return m_error(c,p,"Name expected");
}

function m_number_i(c,p,req) {
  var at = p, val = 0, t=c[p];
  while (t >= 48 && t <= 57) { val=val*10+(t-48); t=c[++p]; }
  if (p > at) {
    return { $:'num', at, val, fmt:'', aft:p }
  }
  if (!req) return null; return m_error(c,p,req);
}

function m_hex(c,p) {
  var at=p++, val=0, t; // ++ "&"
  for (;;) { t=c[p];
    if (t >= 48 && t <= 57) t-=48;
    else if (t >= 65 && t <= 70) t-=55;
    else if (t >= 97 && t <= 102) t-=87;
    else break; val=val*16+t; ++p;
  }
  if (p-1 > at) {
    return { $:'num', at, val, fmt:'&', aft:p }
  }
  return m_error(c,at,"Hex digits expected after &");
}

function m_bin(c,p) {
  var at=p++, val=0, t=c[p]; // ++ "%"
  while (t >= 48 && t <= 49) { val=val*2+(t-48); t=c[++p]; }
  if (p-1 > 10) {
    return { $:'num', at, val, fmt:'%', aft:p }
  }
  return m_error(c,at,"Binary digits expected after %");
}

function m_string_i(c,p,opt) {
  var org = p, at, s = "", t = c[p];
  if (t !== 34) {
    if (opt) return null; return m_error(c,p,"String expected");
  }
  t = c[++p]; at=p; // skip "
  for (;;) {
    while (t >= 32 && t !== 34) t=c[++p]; // exit: t==34/EOL at p
    if (p > at) s += subs(c,at,p); // append segment, excludes p.
    if (t === 34) {
      if (c[p+1] === 34) { // double-quote.
        s += '"'; p+=2; t=c[p]; at=p; continue;
      }
      return { $:'str', at:org, str:s, aft:p+1 }
    } else { // missing closing quote.
      return m_error(c,p,'Missing " before end of line (begins at '+org+')');
    }
  }
}

function m_expr(c,p,opt,min_bp) {
  var t, at, op, lbp, right, left = m_nud(c,p)
  if (left !== null) {
    // infix operator loop.
    for (;;) {
      p = left.aft; t = c[p]; op=''; lbp=3; // comparison.
      while (t === 32) { t = c[++p]; }; at=p; // skip spaces
      switch (t) {
        case 40: { ++p; // "("
          left = m_arr_idx(c,p,at,left); continue;
        }
        case 42: ++p; op='*'; lbp=5; break;
        case 43: ++p; op='+'; lbp=4; break;
        case 45: ++p; op='-'; lbp=4; break;
        case 46: ++p; op='.'; lbp=5; break; // matrix multiply
        case 47: ++p; op='/'; lbp=5; break;
        case 94: ++p; op='^'; lbp=6; break;
        case 60: t = c[++p]; // "<"
          if (t === 62) { ++p; op='<>'; break; }
          else if (t === 61) { ++p; op='<='; break; }
          else if (t === 60) { ++p; op='<<'; break; }
          else { op='<'; }
          break;
        case 61: ++p; op='='; break; // "="
        case 62: t = c[++p]; // ">"
          if (t === 61) { ++p; op='>='; break; }
          else if (t === 62) { ++p;
            if (c[p] === 62) { op='>>>'; break; }
            else { op='>>'; break; }
          } else { op='>'; }
          break;
        case 65: case 97: // "A"
          t = is_kw(c,p,AND,1); if (t) { p=t; op='AND'; lbp=2; }
          break;
        case 68: case 100: // "D"
          t = is_kw(c,p,DIV,2); if (t) { p=t; op='DIV'; lbp=5; }
          break;
        case 69: case 101: // "E"
          t = is_kw(c,p,EOR,3); if (t) { p=t; op='EOR'; lbp=1; }
          break;
        case 77: case 109: // "M"
          t = is_kw(c,p,MOD,3); if (t) { p=t; op='MOD'; lbp=5; }
          break;
        case 79: case 111: // "O"
          t = is_kw(c,p,OR,2); if (t) { p=t; op='OR'; lbp=1; }
          break;
      }
      if (op) {
        // exit this sub-expr if lbp is lower than min_bp.
        if (lbp < min_bp) return left;
        // use 'op' to build an infix expression.
        right = m_expr(c,p,0,lbp);
        left = { $:op, at, left, right, aft:right.aft };
      } else {
        return left;
      }
    }
  }
  if (opt) return null; return m_error(c,p,"Expression expected");
}

function m_nud(c,p) {
  p = skip_ws(c,p);
  var at=p, t = c[p], right;
  switch (t) {
    case 37: return m_bin(c,p); // "%"
    case 38: return m_hex(c,p); // "&"
    case 40: { ++p; // "("
      right = m_expr(c,p,0,0);
      p = skip_ws(c,right.aft);
      if (c[p] != 41) { // ")"
        return m_error(c,p,"Missing ) before end of line (opened at "+(at+1)+")");
      }
      return { $:'()', at, right, aft:p+1 };
    }
    case 45: { ++p; // "-"
      right = m_nud(c,p);
      if (right !== null) {
        if (right.$ === 'num') { // Negative Number Literal
          right.val = -right.val;
          return right;
        }
        return { $:'neg', at, right, aft:right.aft }
      }
      return m_error(c,p,"Expression expected after '-' sign");
    }
    case 34: { // '"'
      return m_string_i(c,p,0);
    }
    case 70: case 102: t = c[p+1]; // "F"
      if (t === 78 || t === 110) { // "N"
        return m_fn_proc(c,p+2,at,'fn');
      }
      break;
    case 78: case 110: // "N"
      t = is_kw(c,p,NOT,2);
      if (t) {
        right = m_expr(c,t,0,0);
        return { $:'not', at, right, aft:right.aft }
      }
      break;
  }
  var name = m_ident_i(c,p,1,1);
  if (name !== null) {
    // detect built-ins.
    // FIXME: use a switch-matcher like m_stmt.
    var low = name.name.toUpperCase();
    if (name.typ === '') {
      for (var i=0;i<n_funs.length;i++) {
        if (n_funs[i] === low) {
          return m_op_fn(c,name.aft,at,low)
        }
      }
    } else if (name.typ === '$') {
      for (var i=0;i<s_funs.length;i++) {
        if (s_funs[i] === low) {
          return m_op_fn(c,name.aft,at,low+'$')
        }
      }
    }
    return name;
  }
  var num = m_number_i(c,p,'');
  if (num !== null) { p=num.aft;
    if (c[p] === 46) { // "."
      var fr = m_number_i(c,p+1,''); // fraction part (move to m_number_i)
      if (fr) {
        num.i = num.val; num.dec = fr.val; // save parts
        num.val += Math.pow(10,-(fr.aft-fr.at))*fr.val; num.aft=fr.aft;
      }
    }
    return num;
  }
  return null;
}

function m_op_fn(c,p,at,op) {
  var s, args=[]; p = skip_ws(c,p);
  if (c[p] === 40) { // "(" optional args.
    s=p; p = m_args(c, p+1, args);
    if (c[p] === 41) ++p; // ")"
    else err = m_error(c,p,"Missing ) to end arguments (opened at "+s+")");
  }
  return { $:op, at, args, aft:p }
}

function m_args(c,p,args) {
  for (;;) {
    var arg = m_expr(c,p,0,0);
    args.push(arg);
    p = skip_ws(c, arg.aft);
    if (c[p] === 44) { ++p; continue; } // ","
    else break;
  }
  return p;
}

function m_arr_idx(c,p,at,left) {
  var args=[], err=null;
  p = m_args(c,p,args);
  if (c[p] === 41) ++p; // ")"
  else err = m_error(c,p,"Missing ) in array indexing (opened at "+(at+1)+")");
  return { $:'idx', at, left, args, err, aft:p+1 };
}

function m_fn_proc(c,p,at,op) {
  p = skip_ws(c,p);
  var name = m_ident_i(c,p,0,0), args=[], err=null;
  p = skip_ws(c,name.aft);
  if (c[p] === 40) { // "(" optional args.
    p = m_args(c, p+1, args);
    if (c[p] === 41) ++p; // ")"
    else err = m_error(c,p,"Missing ) to end arguments (opened at "+(at+1)+")");
  }
  return { $:op, at, name, args, err, aft:p }
}

function is_kw(c,p,kw,min) {
  while (c[p] === 32) ++p; // skip spaces
  for (var t, dot=p+min, i=0; i<kw.length; i+=2) { t = c[p];
    if (t === kw[i] || t === kw[i+1]) p++; // character matches.
    else if (t === 46 && p >= dot) return p+1; // dot shorthand.
    else return 0; // no match.
  }
  return p; // after keyword.
}

function m_line(text) {
  var c = enc.encode(text), stmts=[], t, p, no=-1, err;
  p = skip_ws(c,0);
  t = m_number_i(c,p,0);
  if (t) { no=t.val; p=t.aft; }
  p = m_stmts(c,p,'',stmts); p = skip_ws(c,p);
  if (p < c.length) {
    if (stmts.length) err = m_error(c,p,"End of Line expected");
    else err = m_error(c,p,"Unrecognised statement");
    p=err.aft;
  }
  return { no, stmts, err }
}

function fmt_code(code) {
  var res=[];
  for (var L of code) {
    var s = fmt_stmts(L.stmts);
    if (L.err) s = fmt_err(L.err, s);
    s = L.no+' '+s;
    res.push(s);
    console.log(s);
  }
  return res;
}
function fmt_stmts(stmts) {
  var s = '';
  for (var S of stmts) {
    if (s) s += ' : ';
    s += fmt_stmt(S);
    if (S.err) s = fmt_err(S.err, s);
  }
  return s;
}
function fmt_err(L,s) {
  if (s) s += ' ';
  return s+`[${L.msg} at ${L.at+1}]`
}
function fmt_stmt(L) {
  switch (L.$) {
    case 'rem': return `rem ${L.text}`;
    case 'let': return `let ${L.name.name}${L.name.typ} = ${fmt_expr(L.exp)}`;
    case 'dim': return `dim`;
    case 'if': {
      var s = 'if '+fmt_expr(L.cond)+' then '+fmt_stmts(L.then_s);
      if (L.else_s.length) s += ' else '+fmt_stmts(L.else_s);
      return s;
    }
    case 'proc': return 'proc '+L.name.name+fmt_args(L.args);
    case 'goto': return `goto ${L.line}`;
    case 'gosub': return `gosub ${L.line}`;
    case 'return': return `return`;
    case 'print': return fmt_print(L);
    default: return 'UNKNOWN';
  }
}
var sems = ['',';',', '," ' "]
function fmt_print(L) {
  var s='print ', v=L.vals, sem, exp;
  for (var i=0; i<v.length; i+=2) {
    sem = v[i]; exp = v[i+1];
    s += sems[sem] + fmt_expr(exp);
  }
  if (L.ts) s += ';';
  return s;
}
function fmt_expr(L) {
  switch (L.$) {
    case 'tab': { var s = 'TAB('+fmt_expr(L.x); if (L.y) s += ','+fmt_expr(L.y); return s+')'; }
    case 'err': return `[${L.msg} at ${L.at+1}]`;
    case '()': return '('+fmt_expr(L.right)+')';
    case 'fn': return 'fn '+L.name.name+fmt_args(L.args);
    case 'neg': return '- '+fmt_expr(L.right);
    case 'not': return 'not '+fmt_expr(L.right);
    case 'name': return L.name+L.typ;
    case 'str': return '"'+L.str.replace(/"/g,'""')+'"';
    case 'num':
      if (L.fmt === '&') return '&'+L.val.toString(16);
      if (L.fmt === '%') return '%'+L.val.toString(2);
      return L.val.toString();
    default:
      if (L.args) return L.$+fmt_args(L.args); // built-ins.
      return fmt_expr(L.left)+' '+L.$+' '+fmt_expr(L.right);
    }
}
function fmt_args(args) {
  var a, len=args.length, s='';
  if (len > 0) { s += '(';
    for (a=0;a<len;a++) {
      if (s.length>1) s += ',';
      s += fmt_expr(args[a]);
    } s += ')';
  }
  return s;
}

var basic = `
10 REM TEMPERATURE CONVERSION (GOSUB VERSION)
20 REM WITHOUT STRUCTURED BASIC
30 REM THIS IS NOT THE WAY TO WRITE PROGRAMS!
40 REM JOHN A COLL
50 REM VERSION 1.0 /22 NOV 81
60 MODE 7
70 @%=&2020A :REM 02 dec places 10 cols, default @%=10
80 PRINT "ENTER THE TEMPERATURE FOLLOWED BY"
90 PRINT "THE FIRST LETTER OF THE TEMPERATURE"
100 PRINT "SCALE. e.g. 100C or 72F or 320K"
110 PRINT
120 PRINT "Enter the temperature ";
130 INPUT REPLY$
140 TEMP=VAL(REPLY$)
150 SCALE$=RIGHT$(REPLY$,1)
160 GOODSCALE=FALSE
170 IF SCALE$="C" THEN GOSUB 370
180 IF SCALE$="F" THEN GOSUB 390
190 IF SCALE$="K" THEN GOSUB 430
200 IF NOT ( GOODSCALE AND TEMP>=-273.16) GOTO 260
210 PRINT''
220 PRINT TEMP; " Celsius"
230 PRINT TEMP+273.16; " Kelvin"
240 PRINT TEMP*9/5 + 32; " Fahrenheit"
250 PRINT
260 IF GOODSCALE THEN 310
270 CLS
280 PRINT "You must follow the temperature with"
290 PRINT "the letter ""C"", ""F"" or ""K"" "
300 PRINT "and nothing else"
310 IF TEMP>=-273.16 THEN 360
320 CLS
330 PRINT "The temperature you have given is"
340 PRINT "too cold for this universe! Try again"
350 PRINT
360 GOTO 110
370 GOODSCALE=TRUE
380 GOTO 460
390 REM CONVERT TO CELSIUS
400 TEMP=(TEMP-32)*5/9
410 GOODSCALE=TRUE
420 GOTO460
430 REM CONVERT TO CELSIUS
440 TEMP=TEMP-273.16
450 GOODSCALE=TRUE
460 RETURN
`;

// var lines = [
//   'IFA=1PRINT"Y"ELSE40',
//   'IF A=2+3*4 OR A=2^7+FN_x(2,b) THEN PRINT "Y" ELSE GOTO 40',
//   'DIMa$(6),bb(x+1),c%(3,2,1)',
//   'LETx%=2^7+1:y=5',
//   'IFA=1PRINT"Y":A=2ELSEA=5',
//   'PRINT"DO YOU WANT INSTRUCTIONS?";:G$=GET$:IFG$="Y"ORG$="y"PROCinstruct',
//   'LET TODAY=23', // starts with TO
//   'LET PRINT=1234.56', // PRINT is a reserved word
// ];

var lines = basic.split('\n'), code=[];
for (var zz of lines) {
  if (zz) code.push(m_line(zz));
}
console.log(JSON.stringify(code,null,2));
fmt_code(code);

})();
