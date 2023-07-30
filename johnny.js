"use strict";
(function(){

var enc = new TextEncoder(), dec = new TextDecoder(); // utf-8

function kw(caps) { // "THEN" => U8[84,116, 72,104, 69,101, 78,110]
  var i, b = enc.encode(caps), v = new Uint8Array(b.length*2), p=0;
  for (i=0; i<b.length; i++) { v[p++] = b[i]; v[p++] = b[i]+32; } // +32 to lower-case.
  return v;
}

var LET=kw("LET"),DIM=kw("DIM"),THEN=kw("THEN"),ELSE=kw("ELSE"),FOR=kw("FOR"),NEXT=kw("NEXT");
var REPEAT=kw("REPEAT"),WHILE=kw("WHILE"),CASE=kw("CASE"),END=kw("END"),GOTO=kw("GOTO");
var GOSUB=kw("GOSUB"),RETURN=kw("RETURN"),READ=kw("READ"),RESTORE=kw("RESTORE"),SET=kw("SET");
var PRINT=kw("PRINT"),PROC=kw("PROC"),AND=kw("AND"),OR=kw("OR"),EOR=kw("EOR"),NOT=kw("NOT");

function log(c,p,msg) {
  console.log(`${msg} ${subs(c,p-4,p+5)}\n${'^'.padStart(msg.length+6)}`);
}

function isAlpha(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122); }
function rest(c,p) { return dec.decode(c.slice(p)); }
function subs(c,s,e) { return dec.decode(c.slice(s,e)); }
function skip_ws(c,p) { while (c[p] === 32) ++p; return p; }

function m_error(c,p,msg) {
  p = skip_ws(c,p);
  return { $:'error', msg, col:p+1, text:rest(c,p), aft:c.length }
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
    case 68: case 100: {  // "D"
      t = is_kw(c,p,DIM,3);
      if (t) return m_dim(c,t,at);
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
      if (t) return m_fn_proc(c,t,at,'PROC');
      break;
    }
    case 63: { // "?" shorthand for PRINT.
      return m_print(c,p,at);
    }
    case 71: case 103: { // "G"
      t = is_kw(c,p,GOTO,1);
      if (t) return m_goto_line(c,t,"Expecting a line number after GOTO");
      break;
    }
  }
  s = m_let(c,p,at,1); if (s) return s;
  if (!req) return null; // no match.
  return m_error(c,at,'Unrecognised Statement after '+req+' (Statement expected)')
}

function m_let(c,p,at,opt) {
  var name, exp=null, err=null;
  p = skip_ws(c,p);
  name = m_ident_i(c,p,0,1);
  if (name) {
    p = skip_ws(c,name.aft);
    if (c[p] === 61) { // "="
      exp = m_expr(c,p+1,0,0); p=exp.aft;
    } else {
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

function m_print(c,p,at) {
  var t, vals=[]
  for (;;) {
    p = skip_ws(c,p);
    switch (c[p]) {
      case 10: case 13: // EOL
      case 58: // ":"
        return { $:'print', at, vals, aft:p } // End PRINT.
      case 44: // ","
      case 59: // ";"
      case 39: // "'"
        // Print separators - TODO
        p++;
        continue;
      case 69: case 101: { // "E"
        if (is_kw(c,p,ELSE,2)) {
          // Must exit PRINT before ELSE,
          // in case this statement is inside an IF-ELSE.
          return { $:'print', at, vals, aft:p }
        }
      }
    }
    var expr = m_expr(c,p,1,0)
    if (expr !== null) {
      vals.push(expr); p = expr.aft;
    } else {
      vals.push(m_error(c,p,"Expecting an expression print in PRINT statement"));
      return { $:'print', at, vals, aft:c.length }
    }
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
  var at = p, t = c[p], typ = '';
  while (isAlpha(t) || t === 95) t=c[++p];
  if (p > at) {
    if (suf) {
      if (t === 37) { ++p; typ='%' } // "%"
      else if (t === 36) { ++p; typ='$' } // "$"
    }
    return { $:'name', at, name:subs(c,at,p), typ, aft:p }
  }
  if (opt) return null; return m_error(c,p,"Name expected");
}

function m_number_i(c,p,req) {
  var at = p, val = 0, t = c[p];
  while (t >= 48 && t <= 57) { val=val*10+(t-48); t=c[++p]; }
  if (p > at) {
    return { $:'num', at, val, aft:p }
  }
  if (!req) return null; return m_error(c,p,req);
}

function m_string_i(c,p,opt) {
  var org = p, at, s = "", t = c[p];
  if (t !== 34) {
    if (opt) return null; return m_error(c,p,"String expected");
  }
  t = c[++p]; at=p; // advance.
  for (;;) {
    while (t !== 34 && t > 13) t=c[++p];
    if (p > at) s += subs(c,at,p); at=p; // append segment.
    if (t === 34) {
      if (c[p+1] === 34) { // double-quote.
        s += '"'; p += 2; t = c[p];
        continue;
      } else { // closing quote.
        return { $:'str', at:org, str:s, aft:p+1 }
      }
    } else { // missing closing quote.
      return m_error(c,p,"Missing \" before end of line");
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
    case 40: { ++p; // "("
      right = m_expr(c,p,0,0);
      p = skip_ws(c,right.aft);
      if (c[p] != 41) { // ")"
        return m_error(c,p,"Missing ) before end of line (opened at "+(at+1)+")");
      }
      right.aft = p+1;
      return right;
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
        return m_fn_proc(c,p+2,at,'FN');
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
  if (name !== null) return name;
  var num = m_number_i(c,p,"");
  if (num !== null) return num;
  return null;
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
  for (var t, dot=p+min, i=0; i<kw.length; i+=2) {
    t = c[p];
    if (t === kw[i] || t === kw[i+1]) {
      p++; // character matches, advance past it.
    } else if (t === 46 && p >= dot) {
      return p+1; // dot shorthand.
    } else {
      return 0; // charcter mismatch.
    }
  }
  return p; // after keyword.
}

function m_line(text) {
  var c = enc.encode(text), stmts=[], err;
  var p = m_stmts(c,0,'NL',stmts); p = skip_ws(c,p);
  if (p < c.length) { err = m_error(c,p,"End of Line expected"); p=err.aft; }
  return { $:'line', stmts, err }
}

var lines = [
  'IFA=1PRINT"Y"ELSE40',
  'IF A=2+3*4 OR A=2^7+FN_x(2,b) THEN PRINT "Y" ELSE GOTO 40',
  'DIMa$(6),bb(x+1),c%(3,2,1)',
  'LETx%=2^7+1:y=5',
  'IFA=1PRINT"Y":A=2ELSEA=5',
  'PRINT"DO YOU WANT INSTRUCTIONS?";:G$=GET$:IFG$="Y"ORG$="y"PROCinstruct',
];

for (var zz of lines) {
  console.log(JSON.stringify(m_line(zz),null,2));
}

})();
