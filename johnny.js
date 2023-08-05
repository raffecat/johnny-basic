"use strict";
(function(D,W){
function El(n){return D.getElementById(n)}
function ElT(n){return D.getElementsByTagName(n)[0]}
function Show(n){var e=El(n);if(e)e.style.display='block'}
function Hide(n){var e=D.getElementById(n);if(e)e.style.display='none'}
function Tag(n,c){var t=D.createElement(n);if(c)t.className=c;return t}
function JBrt(){
var enc = new TextEncoder(), dec = new TextDecoder(); // utf-8

function kw(caps) { // "THEN" => U8[84,116, 72,104, 69,101, 78,110]
  var i, b = enc.encode(caps), v = new Uint8Array(b.length*2), p=0;
  for (i=0; i<b.length; i++) { v[p++] = b[i]; v[p++] = b[i]+32; } // +32 to lower-case.
  return v;
}

var REM=kw("REM"),LET=kw("LET"),DIM=kw("DIM"),THEN=kw("THEN"),ELSE=kw("ELSE"),FOR=kw("FOR"),TO=kw("TO"),NEXT=kw("NEXT");
var INPUT=kw("INPUT"),REPEAT=kw("REPEAT"),UNTIL=kw("UNTIL"),WHILE=kw("WHILE"),CASE=kw("CASE"),END=kw("END"),GOTO=kw("GOTO"),TAB=kw("TAB");
var GOSUB=kw("GOSUB"),RETURN=kw("RETURN"),DATA=kw("DATA"),READ=kw("READ"),RESTORE=kw("RESTORE"),CLS=kw("CLS"),LINE=kw("LINE");
var PRINT=kw("PRINT"),PROC=kw("PROC"),DIV=kw("DIV"),MOD=kw("MOD"),AND=kw("AND"),OR=kw("OR"),EOR=kw("EOR"),NOT=kw("NOT");
var MODE=kw("MODE"),COLOUR=kw("COLOUR"),COLOR=kw("COLOR"),GCOL=kw("GCOL"); // BBC
var MOVE=kw("MOVE"),DRAW=kw("DRAW"),PLOT=kw("PLOT"),VDU=kw("VDU"); // BBC
var b_funs = {
  'GET':0,'INKEY':0,'RND':1,'TIME':0,'DIM':2,
  'FLOOR':1,'CEIL':1,'ABS':1,'ATN':1,'COS':1,'EXP':1,'INT':1,'SGN':1,'SIN':1,'SQR':1,'LOG':1,'LN':1,'TAN':1,
  'LEN':1,'INSTR':0,'ASC':1,'VAL':1,
  'GET$':0,'INKEY$':0,'LEFT$':2,'MID$':3,'RIGHT$':2,'STRING$':2,'CHR$':1,'STR$':1,'BIN$':1,'HEX$':1,'AT$':2,'UPPER$':1,'LOWER$':1
};

function log(c,p,msg) {
  console.log(`${msg} ${subs(c,p-4,p+5)}\n${'^'.padStart(msg.length+6)}`);
}

function isAlpha(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95 || c === 64; } // [A-Za-z_@]
//function rest(c,p) { return dec.decode(c.slice(p)); }
function subs(c,s,e) { return dec.decode(c.slice(s,e)); }
function skip_ws(c,p) { while (c[p] === 32) ++p; return p; }

var ev=[];
function m_error(c,p,msg) {
  var at = skip_ws(c,p);
  while (p<c.length && c[p]!==58) ++p; // up to ":"
  ev.push(at, msg, subs(c,at,p));
  return { $:'err', aft:p }
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
      return m_print(c,p+1,at);
    }
    case 67: case 99: { // "C"
      t = is_kw(c,p,CLS,3);
      if (t) return { $:'cls', at, aft:t }
      t = is_kw(c,p,COLOR,1);
      if (t) return m_color(c,t,at);
      t = is_kw(c,p,COLOUR,1);
      if (t) return m_color(c,t,at);
      break;
    }
    case 68: case 100: {  // "D"
      t = is_kw(c,p,DIM,3);
      if (t) return m_dim(c,t,at);
      t = is_kw(c,p,DRAW,2);
      if (t) return m_draw(c,t,at);
      break;
    }
    case 70: case 102: { // "F"
      t = is_kw(c,p,FOR,1);
      if (t) return m_for(c,t,at);
      break;
    }
    case 71: case 103: { // "G"
      t = is_kw(c,p,GOTO,1);
      if (t) return m_goto_line(c,t,"Expecting a line number after GOTO");
      t = is_kw(c,p,GOSUB,3);
      if (t) return m_goto_line(c,t,"Expecting a line number after GOTO");
      t = is_kw(c,p,GCOL,2);
      if (t) return m_gcol(c,t,at);
      break;
    }
    case 73: case 105: { t = c[p+1]; // "I"
      if (t === 70 || t === 102) {   // "F"
        return m_if(c,p+2,at);
      }
      t = is_kw(c,p,INPUT,1);
      if (t) return m_input(c,t,at);
      break;
    }
    case 76: case 108: { // "L"
      t = is_kw(c,p,LET,3);
      if (t) return m_let(c,t,at,0);
      break;
    }
    case 77: case 109: { // "M"
      t = is_kw(c,p,MODE,2);
      if (t) return m_mode(c,t,at);
      t = is_kw(c,p,MOVE,4);
      if (t) return m_move(c,t,at);
      break;
    }
    case 78: case 110: { // "N"
      t = is_kw(c,p,NEXT,1);
      if (t) return { $:'next', at, aft:t }
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
      t = is_kw(c,p,REPEAT,3);
      if (t) return { $:'repeat', at, aft:t }
      break;
    }
    case 85: case 117: { // "U"
      t = is_kw(c,p,UNTIL,1);
      if (t) return m_until(c,t,at);
      break;
    }
    case 86: case 118: { // "V"
      t = is_kw(c,p,VDU,1);
      if (t) return m_vdu(c,t,at);
      break;
    }
  }
  s = m_let(c,p,at,1); if (s) return s;
  if (req) return m_error(c,at,'Unrecognised Statement after '+req+' (Statement expected)')
  return null; // no match.
}

function m_rem(c,p,at) {
  p = skip_ws(c,p);
  return { $:'rem', at, text:subs(c,p,c.length), aft:c.length }
}

function m_mode(c,p,at) {
  p = skip_ws(c,p);
  var mode = m_expr(c,p,0,0);
  return { $:'mode', at, mode, aft:mode.aft };
}
function m_color(c,p,at) {
  p = skip_ws(c,p);
  var col = m_expr(c,p,0,0); p = skip_ws(p,col.aft);
  return { $:'color', at, col, aft:p };
}
function m_gcol(c,p,at) {
  p = skip_ws(c,p);
  var gcol=null, pxop=m_expr(c,p,0,0); p = skip_ws(p,pxop.aft);
  if (c[p] === 44) {
    gcol = m_expr(c,p+1,0,0); p=skip_ws(p,gcol.aft);
  } else return m_error(c,p,"Expecting , in GCOL");
  return { $:'gcol', at, pxop, gcol, aft:p };
}
function m_move(c,p,at) {
  p = skip_ws(c,p);
  var y=null, x=m_expr(c,p,0,0); p=skip_ws(p,x.aft);
  if (c[p] === 44) {
    y = m_expr(c,p+1,0,0); p=skip_ws(p,y.aft);
  } else return m_error(c,p,"Expecting , in MOVE");
  return { $:'move', at, x, y, aft:p };
}
function m_draw(c,p,at) {
  p = skip_ws(c,p);
  var y=null, x=m_expr(c,p,0,0); p=skip_ws(p,x.aft);
  if (c[p] === 44) {
    y = m_expr(c,p+1,0,0); p=skip_ws(p,y.aft);
  } else return m_error(c,p,"Expecting , in DRAW");
  return { $:'draw', at, x, y, aft:p };
}
function m_vdu(c,p,at) {
  var args=[]; p = skip_ws(c,p);
  p = m_args(c,p,args);
  return { $:'vdu', at, args, aft:p };
}

function m_input(c,p,at) {
  // comma causes '?' to be printed. ';' means the same.
  var t, s, line=0, com=0, vars=[];
  p = skip_ws(c,p);
  t = is_kw(c,p,LINE,4);
  if (t) { line=1; p = skip_ws(c,t); }
  if (c[p] === 44) { com=1; p = skip_ws(c,p+1); } // ","
  for (;;) {
    s = m_ident_i(c,p,1,1);
    if (!s) break;
    vars.push(s.name);
    p = skip_ws(c,s.aft);
    if (c[p] === 44) { ++p; continue } // ","
    else break;
  }
  if (vars.length < 1) {
    return m_error(c,p,"Missing variable name");
  }
  return { $:'input', at, com, vars, aft:p };
}

function m_let(c,p,at,opt) {
  var name, exp=null;
  p = skip_ws(c,p);
  name = m_ident_i(c,p,1,1);
  if (name) {
    p = skip_ws(c,name.aft);
    if (c[p] === 61) { // "="
      exp = m_expr(c,p+1,0,0); p=exp.aft;
    } else {
      if (opt) return null; // not a LET stmt!
      return m_error(c,p,"Missing = in Let statement");
    }
  } else {
    if (opt) return null;
    return m_error(c,p,"Missing name in Let statement");
  }
  return { $:'let', at, name:name.name, exp, aft:p }
}

function m_dim(c,p,at) {
  var dims=[], name, args, a0, a1, e0=ev.length;
  for (;;) {
    p = skip_ws(c,p); a0=p;
    name = m_ident_i(c,p,0,1); args=[];
    p = skip_ws(c,name.aft);
    if (c[p] === 40) { a1=p; // "("
      p = m_args(c, p+1, args);
      if (c[p] === 41) ++p; // ")"
      else return m_error(c,p,"Missing ) to end Dim (opened at "+(a1+1)+")");
    } else return m_error(c,p,"Missing ( after name in Dim");
    dims.push({ at:a0, name:name.name, args });
    if (ev.length===e0 && c[p] === 44) { ++p; continue; } // ","
    else break;
  }
  return { $:'dim', at, dims, aft:p }
}

// input: prints a "?"

function m_print(c,p,at) {
  var s, vals=[], sem=0;
  // prior separator is used when terms are juxtaposed!
  // terms can be juxtaposed with or without spaces, until ':' EOL ELSE
  // TAB(c) advances to column c, next line if necessary.
  // numbers always pad to their 10-column width, unless after ;
  pr:for (;;) {
    p = skip_ws(c,p);
    switch (c[p]) {
      case 10: case 13: break pr; // eol end print
      case 39: sem=2; ++p; continue; // "'" begin new line
      case 44: sem=0; ++p; continue; // "," commas create fields
      case 58: break pr; // ":" end print
      case 59: sem=1; ++p; continue; // ";" semis join without gaps
      case 84: case 116: { // "T"
        s = m_tab(c,p,sem);
        if (s) { vals.push(sem,s); p=s.aft; continue; } // TAB()
        break;
      }
      case 69: case 101: { // "E"
        if (is_kw(c,p,ELSE,2)) break pr; // ELSE end print
        break;
      }
      case 34: { // " literal string
        s = m_string_i(c,p,0);
        vals.push(sem, s); p = s.aft;
        continue;
      }
    }
    s = m_expr(c,p,1,0);
    if (s === null) break; // end print
    vals.push(sem, s); p = s.aft;
  }
  p = skip_ws(c,p); sem=0;
  if (c[p] === 59) { sem=1; ++p; } // trailing ";"
  return { $:'print', at, vals, sem, aft:p }
}

function m_tab(c,p,sem) {
  var x, y, t = is_kw(c,p,TAB,3), at=p;
  if (t && c[p+3] === 40) { // "TAB("
    x = m_expr(c,p+4,0,0); p=skip_ws(c,x.aft);
    if (c[p] === 44) { // ","
      y = m_expr(c,p+1,0,0); p=skip_ws(c,y.aft);
    }
    if (c[p] === 41) ++p; else { // ")"
      return m_error(c,p,"Missing ) to end TAB()");
    }
    return { $:'tab', at, sem, x, y, aft:p }
  }
}

function m_if(c,p,at) {
  // IF•{expr}[THEN]{ln/stmt}[ELSE{ln/stmt}]
  var cond, then_s=[], else_s=[], thn, els;
  cond = m_expr(c,p,1,0);
  if (cond === null) {
    return m_error(c,p,"Incomplete IF statement (Condition expected)");
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
      return m_error(c,p,"Missing THEN after IF condition (Statement expected)");
    }
  }
  return { $:'if', at, cond, then_s, else_s, aft:p }
}

function m_for(c,p,at) {
  // FOR•{name}={expr}TO{expr}[STEP{expr}]
  var t, name, from=null, to=null, step=null;
  p = skip_ws(c,p);
  name = m_ident_i(c,p,1,1);
  if (name) {
    p = skip_ws(c,name.aft);
    if (c[p] === 61) { // "="
      from = m_expr(c,p+1,0,0); p=from.aft;
      t = is_kw(c,p,TO,2);
      if (t) {
        to = m_expr(c,t,0,0); p=skip_ws(c,to.aft);
      } else {
        return m_error(c,p,"Missing TO in For statement");
      }
    } else {
      return m_error(c,p,"Missing = in For statement");
    }
  } else {
    return m_error(c,p,"Missing name in For statement");
  }
  return { $:'for', at, name:name.name, from, to, step, aft:p }
}

function m_until(c,p,at) {
  var cond;
  cond = m_expr(c,p,1,0);
  if (cond !== null) p=cond.aft; else {
    return m_error(c,p,"Incomplete UNTIL statement (Condition expected)");
  }
  return { $:'until', at, cond, aft:p }
}

function m_stmts_goto(c,p,req,stmts) {
  var s = m_goto_line(c,p,null);
  if (s !== null) { stmts.push(s); return s.aft; }
  return m_stmts(c,p,req,stmts);
}

function m_goto_line(c,p,stmt) {
  p = skip_ws(c,p);
  var num = m_number_i(c,p,0);
  if (num) {
    // Implicit GoTo (a line number)
    return { $:'goto', at:num.at, line:num.val, exp:null, aft:num.aft }
  }
  if (stmt) { // "goto" stmt:
   var to = m_expr(c,p,1,0); // BBC basic allows "goto <var>"!
   if (to) return { $:'goto', at:num.at, line:0, exp:to, aft:to.aft }
   return m_error(c,p,stmt);
  }
  return null;
}

function m_ident_i(c,p,opt,suf) {
  var at=p, t=c[p];
  while (isAlpha(t)) t=c[++p];
  if (p > at) {
    if (suf && (t === 36 || t === 37)) ++p; // "$","%"
    return { $:'name', at, name:subs(c,at,p), aft:p }
  }
  if (!opt) return m_error(c,p,"Name expected");
  return null;
}

function m_number_i(c,p,req) {
  var at = p, val = 0, t=c[p];
  while (t >= 48 && t <= 57) { val=val*10+(t-48); t=c[++p]; }
  if (p > at) {
    return { $:'num', at, val, fmt:'', aft:p }
  }
  if (req) return m_error(c,p,req);
  return null;
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
    if (!opt) return m_error(c,p,"String expected");
    return null; 
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
      p = left.aft; t = c[p]; op=''; lbp=3; // comparison
      while (t === 32) { t = c[++p]; }; at=p; // skip spaces
      switch (t) {
        case 42: ++p; op='*'; lbp=5; break;
        case 43: ++p; op='+'; lbp=4; break;
        case 45: ++p; op='-'; lbp=4; break;
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
  if (!opt) return m_error(c,p,"Expression expected");
  return null;
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
        right = m_fn_proc(c,p+2,at,'fn');
        return m_may_index(c,right.aft,right);
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
    var up = name.name.toUpperCase();
    if (b_funs.hasOwnProperty(up)) {
      return m_op_fn(c,name.aft,at,up,b_funs[up])
    }
    return m_may_index(c,name.aft,name);
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

function m_may_index(c,p,left) {
  // permitted to use array-indexing.
  p = skip_ws(c,p);
  if (c[p] === 40) { // "("
    return m_arr_idx(c,p+1,p,left);
  }
  return left;
}

function m_op_fn(c,p,at,op,narg) {
  var s,n=narg&15,args=[]; p=skip_ws(c,p);
  if (c[p] === 40) { // "(" optional args.
    s=p; p = m_args(c, p+1, args);
    if (c[p] === 41) { ++p; // ")"
      if (args.length < n) {
        return m_error(c,p,"Function "+op+" requires "+n+" argument"+(n>1?'s':''));
      } else if (args.length > n+(narg>>4)) {
        return m_error(c,p,"Too many arguments to function "+op);
      }
    } else return m_error(c,p,"Missing ) to end arguments (opened at "+s+")");
  } else if (n) {
    return m_error(c,p,"Function "+op+" requires "+n+" argument"+(n>1?'s':''));
  }
  return { $:op, at, args, aft:p }
}

function m_args(c,p,args) {
  for (;;) {
    var arg = m_expr(c,p,0,0);
    if (!arg) break;
    args.push(arg);
    p = skip_ws(c, arg.aft);
    if (c[p] === 44) { ++p; continue; } // ","
    else break;
  }
  return p;
}

function m_arr_idx(c,p,at,left) {
  var args=[];
  p = m_args(c,p,args);
  if (c[p] === 41) ++p; // ")"
  else return m_error(c,p,"Missing ) in array indexing (opened at "+(at+1)+")");
  return { $:'idx', at, left, args, aft:p+1 };
}

function m_fn_proc(c,p,at,op) {
  p = skip_ws(c,p);
  var name = m_ident_i(c,p,0,0), args=[];
  p = skip_ws(c,name.aft);
  if (c[p] === 40) { // "(" optional args.
    p = m_args(c, p+1, args);
    if (c[p] === 41) ++p; // ")"
    else return m_error(c,p,"Missing ) to end arguments (opened at "+(at+1)+")");
  }
  return { $:op, at, name:name.name, args, aft:p }
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
  var c = enc.encode(text), stmts=[], t, p, no=-1, err=null;
  p = skip_ws(c,0);
  t = m_number_i(c,p,0);
  if (t) { no=t.val; p=t.aft; }
  p = m_stmts(c,p,'',stmts); p = skip_ws(c,p);
  if (p < c.length) {
    if (stmts.length) return m_error(c,p,"End of Line expected");
    else return m_error(c,p,"Unrecognised statement");
  }
  if (ev.length) { err=ev; ev=[] }
  return { no, stmts, err }
}

// Regenerate code.

function fmt_code(code) {
  var res=[];
  for (var L of code) {
    var s = fmt_stmts(L.stmts);
    if (L.err) s = fmt_err(L.err, s);
    if (L.no >= 0) s = L.no+' '+s;
    res.push(s);
  }
  return res;
}
function fmt_stmts(stmts) {
  var s = '';
  for (var S of stmts) {
    if (s) s += ' : ';
    s += fmt_stmt(S);
  }
  return s;
}
function fmt_err(ev,s) {
  for (var i=0;i<ev.length;i+=3) {
   if (s) s += ' ';
   s+`[${ev[i+1]} at ${ev[i]+1}: ${ev[i+2]}]`
  }
  return s;
}
function fmt_stmt(L) {
  switch (L.$) {
    case 'rem': return `rem ${L.text}`;
    case 'let': return `let ${L.name} = ${fmt_expr(L.exp)}`;
    case 'dim': return `dim`;
    case 'if': {
      var s = 'if '+fmt_expr(L.cond)+' then '+fmt_stmts(L.then_s);
      if (L.else_s.length) s += ' else '+fmt_stmts(L.else_s);
      return s;
    }
    case 'for': {
      var s = 'for '+L.name+' = '+fmt_expr(L.from)+' to '+fmt_expr(L.to);
      if (L.step) s += ' step '+fmt_expr(L.step);
      return s;
    }
    case 'next': return 'next';
    case 'repeat': return 'repeat';
    case 'until': return 'until '+fmt_expr(L.cond);
    case 'proc': return 'proc '+L.name+fmt_args(L.args,1);
    case 'goto': return `goto ${L.line}`;
    case 'gosub': return `gosub ${L.line}`;
    case 'return': return `return`;
    case 'print': return fmt_print(L);
    case 'input': return fmt_input(L);
    case 'cls': return 'cls';
    case 'mode': return 'mode '+fmt_expr(L.mode);
    case 'color': return 'color '+fmt_expr(L.col);
    case 'gcol': return 'gcol '+fmt_expr(L.pxop)+', '+fmt_expr(L.gcol);
    case 'move': return 'move '+fmt_expr(L.x)+', '+fmt_expr(L.y);
    case 'draw': return 'draw '+fmt_expr(L.x)+', '+fmt_expr(L.y);
    case 'vdu': return 'vdu '+fmt_args(L.args,0);
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
  if (L.sem) s += ';';
  return s;
}
function fmt_input(L) {
  var s='', v=L.vars, it;
  for (var i=0; i<v.length; i++) {
    it = v[i]; if (s) s += ', ';
    s += fmt_expr(it);
  }
  if (L.com) s = ','+s;
  return 'input '+s;
}
function fmt_expr(L) {
 switch (L.$) {
  case 'tab': { var s = 'TAB('+fmt_expr(L.x); if (L.y) s += ','+fmt_expr(L.y); return s+')'; }
  case 'err': return `[${L.msg} at ${L.at+1}]`;
  case '()': return '('+fmt_expr(L.right)+')';
  case 'fn': return 'fn '+L.name+fmt_args(L.args,1);
  case 'neg': return '- '+fmt_expr(L.right);
  case 'not': return 'not '+fmt_expr(L.right);
  case 'name': return L.name;
  case 'str': return '"'+L.str.replace(/"/g,'""')+'"';
  case 'num':
   if (L.fmt === '&') return '&'+L.val.toString(16);
   if (L.fmt === '%') return '%'+L.val.toString(2);
   return L.val.toString();
  default:
   if (L.args) return L.$+fmt_args(L.args,1); // built-ins.
   return fmt_expr(L.left)+' '+L.$+' '+fmt_expr(L.right);
 }
}
function fmt_args(args,wrap) {
  var a, len=args.length, s='';
  if (len > 0) {
    if (wrap) s += '(';
    for (a=0;a<len;a++) {
      if (s.length>1) s += ',';
      s += fmt_expr(args[a]);
    }
    if (wrap) s += ')';
  }
  return s;
}

// CodeGen.

var opLet=1|0,opDim=2|0,opPrint=3|0,opIfN=4|0,opJmp=5|0,opGoToExp=6|0,opGoSubExp=7|0,opReturn=8|0,opInput=9|0,opNext=10|0;
var opNeg=11|0,opNot=12|0,opVar=13|0,opNum=14|0,opStr=15|0,opFn=16|0,opTab=17|0,opTabXY=18|0,opFor=19|0;
var opAdd=20|0,opSub=21|0,opMul=22|0,opDiv=23|0,opIDiv=24|0,opMod=25|0,opPow=26|0,opAnd=27|0,opOr=28|0,opEor=29|0;
var opEq=30|0,opNe=31|0,opGt=32|0,opGe=33|0,opLt=34|0,opLe=35|0,opRepeat=36|0,opUntil=37|0;
var opInKey=38|0,opSqr=39|0;
var opMode=50|0,opCls=51|0,opColor=52|0,opGCol=53|0,opMove=54|0,opDraw=55|0,opVdu=56|0; // BBC
var opCodes={
 '+':opAdd,'-':opSub,'*':opMul,'/':opDiv,'DIV':opIDiv,'MOD':opMod,'^':opPow,
 'AND':opAnd,'OR':opOr,'EOR':opEor,'=':opEq,'<>':opNe,'<':opLt,'<=':opLe,'>':opGt,'>=':opGe,
 'INKEY':opInKey,'SQR':opSqr,
};
function new_gctx() {
 return {ops:[],sol:[],sos:[],err:[],line:0|0,nvar:0|0,varmap:new Map(),vars:[],out:[]}
}
function gen_code(code, G) {
 G.ops=[""]; G.ops.length=0; G.sol=[]; G.sos=[]; G.err=[]; // new outputs.
 for (var L of code) {
  G.line = L.no|0;
  G.sol.push(G.line,G.ops.length); // start of line.
  if (L.err) gen_err(G,L.err); else gen_stmts(G,L.stmts);
 }
}
function gen_err(G,ev) { // only 1st
 if (G.line>=0) G.err.push(ev[1]+' at line '+G.line); else G.err.push(ev[1]);
}
function gen_bad(G) {
 if (!G.err.length) G.err.push("Bad code"); // fallback.
}
function gen_var(G,name) {
 if (typeof name !== 'string') throw 1;
 var vn,v=G.varmap; if (v.has(name)) return v.get(name)|0;
 vn=G.nvar++; v.set(name,vn); return vn|0;
}
function gen_stmts(G,stmts) {
 var sn=0|0;
 for (var S of stmts) {
   G.sos.push(sn++,G.ops.length); // start of stmt.
   gen_stmt(G,S);
 }
 return s;
}
function gen_stmt(G,L) {
 switch (L.$) {
   case 'rem': return
   case 'let': {
    if (!(L.name && L.exp)) return gen_bad(G);
    var vn = gen_var(G,L.name);
    push_expr(G,L.exp); G.ops.push(opLet,vn); return;
   }
   case 'dim': { var dims=L.dims,i,dim,vn;
    for (i=0;i<dims;i++) {
     dim=dims[i]; push_args(G,dim.args);
     vn = gen_var(G,dim.name.type);
     G.ops.push(opDim,vn,dim.args.length);
    }
    return;
   }
   case 'if': { var j_ov,j_ex;
    if (!(L.cond)) return gen_bad(G);
    push_expr(G,L.cond); G.ops.push(opIfN,0); j_ov=G.ops.length-1;
    gen_stmts(G,L.then_s);
    if (L.else_s.length) {
     G.ops[j_ov] = G.ops.length; // patch jmp-over.
     G.ops.push(opJmp,0); j_ex=G.ops.length-1;
     gen_stmts(G,L.else_s);
     G.ops[j_ex] = G.ops.length; // patch jmp-exit.
    } else {
     G.ops[j_ov] = G.ops.length; // patch jmp-over.
    }
    return;
   }
   case 'for': {
    if (!(L.name && L.from && L.to)) return gen_bad(G);
    push_expr(G,L.from); push_expr(G,L.to); G.ops.push(opFor,gen_var(G,L.name));
    return;
   }
   case 'next': G.ops.push(opNext); return;
   case 'repeat': G.ops.push(opRepeat); return;
   case 'until': push_expr(G,L.cond); G.ops.push(opUntil); return;
   case 'proc': return gen_bad(G); // TODO.
   case 'goto': {
    if (L.exp) { push_expr(G,L.exp); G.ops.push(opGoToExp); return; }
    G.ops.push(opNum,L.line); G.ops.push(opGoToExp); return; // use dynamic for now.
   }
   case 'gosub': {
    if (L.exp) { push_expr(G,L.exp); G.ops.push(opGoSubExp); return; }
    G.ops.push(opNum,L.line); G.ops.push(opGoSubExp); return; // use dynamic for now.
   }
   case 'return': G.ops.push(opReturn); return;
   case 'print': gen_print(G,L); return;
   case 'input': gen_input(G,L); return;
   case 'cls': G.ops.push(opCls); return;
   case 'mode': push_expr(G,L.mode); G.ops.push(opMode); return;
   case 'color': push_expr(G,L.col); G.ops.push(opColor); return;
   case 'gcol': push_expr(G,L.pxop); push_expr(G,L.gcol); G.ops.push(opGCol); return;
   case 'move': push_expr(G,L.x); push_expr(G,L.y); G.ops.push(opMove); return;
   case 'draw': push_expr(G,L.x); push_expr(G,L.y); G.ops.push(opDraw); return;
   case 'vdu': push_args(G,L.args); G.ops.push(opVdu,L.args.length); return;
   default: gen_err(G,[L.at,"Unknown statement: "+L.$,'']);
 }
}
function gen_print(G,L) {
 var i,vals=L.vals,sems=[];
 for (i=vals.length-2;i>=0;i-=2) { // reversed.
  sems.push(vals[i]|0);
  push_expr(G,vals[i+1]);
 }
 G.ops.push(opPrint, sems.length, ...sems, L.sem|0);
}
function gen_input(G,L) {
 var i,v,vars=L.vars,vns=[];
 for (i=0;i<vars.length;i++) { v=vars[i];
  vns.push(gen_var(G,v));
 }
 G.ops.push(opInput, L.com|0, vars.length, ...vns);
}
function push_args(G,args) {
  for (var i=0;i<args.length;i++) push_expr(G,args[i]);
}
function push_expr(G,L) {
 if (L===undefined) return gen_bad(G);
 switch (L.$) {
  case 'tab': {
   push_expr(G,L.x);
   if (L.y) { push_expr(G,L.y); G.ops.push(opTabXY); return }
   G.ops.push(opTab); return
  }
  case '()': push_expr(G,L.right); return
  case 'fn': {
   for (var i=0;i<L.args.length;i++) push_expr(G,L.args[i]);
   var n = gen_var(G,'fn:',L.name);
   G.ops.push(opFn,n); return
  }
  case 'neg': push_expr(G,L.right); G.ops.push(opNeg); return
  case 'not': push_expr(G,L.right); G.ops.push(opNot); return
  case 'name': {
   var n = gen_var(G,L.name);
   G.ops.push(opVar,n); return
  }
  case 'num': G.ops.push(opNum,L.val); if (typeof L.val !== 'number') throw 1; return
  case 'str': G.ops.push(opStr,L.str); return
  default: {
   var op=opCodes[L.$]|0; if (!op) {
    G.err.push("Missing opcode for "+L.$);
   } else {
    if (L.args) {
      for (var i=0;i<L.args.length;i++) push_expr(G,L.args[i]); G.ops.push(op); return
    } else {
      push_expr(G,L.left); push_expr(G,L.right); G.ops.push(op); return
    }
   }
  }
 }
}

// Evaluator.

function eval_code(ops, G) {
 var a=G.vars,i,n,stack=[],top=0,p=0; G.out=[]; // reset output.
 for (i=a.length;i<G.nvar;i++) a.push(null); // alloc vars.
 for (p=0;p<ops.length;) {
  switch (ops[p++]) {
  case opLet: G.vars[ops[p++]] = stack[--top]; break;
  case opDim: {
   n=ops[p++]; i=ops[p++];
   G.vars[n]=[]; G.dims[n]=(a=[]);
   while (i--) a.push(stack[--top]); // copy dims to G.dims[n]
   break;
  }
  case opPrint: { // nsems, ...sems, last-sem
   i=ops[p++]; a='';
   while (i--) { n=ops[p++]; // 0=, 1=; 2='
    if (a) a += ' '; a += (stack[--top]||'').toString();
   }
   n=ops[p++]; if (!n) a += "\n"; // last-sem.
   G.out.push(a); break;
  }
  case opIfN: {
   i=ops[p++]; n=stack[--top]; if (!n) p=i; break; // jump.
  }
  case opJmp: p=ops[p++]; break;
  // case opGoToExp: break;
  // case opGoSubExp: break;
  // case opReturn: break;
  // case opInput: break;
  // case opCls: break;
  case opNeg: stack[top] = - stack[top]; break;
  case opNot: stack[top] = ~ stack[top]; break;
  case opVar: n=G.vars[ops[p++]]; stack[top++]=n; break;
  case opNum: stack[top++] = ops[p++]; break;
  case opStr: stack[top++] = ops[p++]; break;
  // case opFn: break;
  // case opTab: break;
  // case opTabXY: break;
  case opAdd: --top; stack[top-1] += stack[top]; break;
  case opSub: --top; stack[top-1] -= stack[top]; break;
  case opMul: --top; stack[top-1] *= stack[top]; break;
  case opDiv: --top; stack[top-1] /= stack[top]; break;
  case opIDiv: --top; stack[top-1] = Math.floor(stack[top-1] / stack[top]); break;
  case opMod: --top; stack[top-1] %= stack[top]; n % i; break;
  case opPow: --top; stack[top-1] = Math.pow(stack[top-1], stack[top]); break;
  case opAnd: --top; stack[top-1] = stack[top-1] & stack[top]; break;
  case opOr: --top; stack[top-1] = stack[top-1] | stack[top]; break;
  case opEor: --top; stack[top-1] = stack[top-1] ^ stack[top]; break;
  case opEq: --top; stack[top-1] = stack[top-1] == stack[top] ? -1 : 0; break;
  case opNe: --top; stack[top-1] = stack[top-1] != stack[top] ? -1 : 0; break;
  case opGt: --top; stack[top-1] = stack[top-1] > stack[top] ? -1 : 0; break;
  case opGe: --top; stack[top-1] = stack[top-1] >= stack[top] ? -1 : 0; break;
  case opLt: --top; stack[top-1] = stack[top-1] < stack[top] ? -1 : 0; break;
  case opLe: --top; stack[top-1] = stack[top-1] <= stack[top] ? -1 : 0; break;
  case opSqr: stack[top-1] = Math.sqrt(stack[top-1]); break;
  default: G.out.push('Not implemented'); return; // throw new Error('bad op '+ops[--p]);
  }
 }
}

// Glue.

function compile_text(text, G) {
 var i,ln,lines = text.split('\n'), code=[];
 for (i=0;i<lines.length;i++) {
   ln=lines[i]; if (ln) code.push(m_line(ln));
 }
 console.log(fmt_code(code).join('\n'));
 gen_code(code, G);
 console.log(JSON.stringify(G,null,2));
 return G;
}

function exec_line(line, G) {
 var code = [m_line(line)]; G.out=[];
 gen_code(code, G); // -> ops,err updates nvar,varmap
 console.log(JSON.stringify(G,null,2));
 if (G.err.length) return G.err.join('\n');
 eval_code(G.ops, G); // -> vars,out
 return G.out.join('');
}

// Scratchpad.

var css = ".hjs{display:none}#inp{display:none;position:absolute;z-index:0;border:0;padding:0;margin:0;outline:0;font:18px monospace;line-height:24px;width:100%;background:#f2f2f2;color:#303335}.sbox{border:1px solid #727272;padding:1px 4px 1px 26px;font:18px monospace;line-height:24px;white-space:nowrap;position:relative;height:98px;overflow-y:scroll;background:#fdfaf9;color:#303335}.sbcr{-webkit-user-select:none;-ms-user-select:none;user-select:none;position:absolute;left:1px;top:1px;width:12px;padding:1px 4px;color:#877c7c;background:#ccc;min-height:96px;}.scode{position:absolute;left:27px;top:1px;bottom:1px;right:3px}.C{height:24px}.RR{height:24px}.CC{position:relative;top:-2px;height:24px}.R{height:24px;font-weight:600}@media(prefers-color-scheme:dark){.sbox{background:#383e41;color:#fff}#inp{background:#414a4e;color:#fff}}.light .sbox{background:#fdfaf9;color:#303335}.light #inp{background:#f2f2f2;color:#303335}.dark .sbox{background:#383e41;color:#fff}.dark #inp{background:#414a4e;color:#fff}";
var h=ElT('head'),s=Tag('style');s.styleSheet?s.styleSheet.cssText=css:s.textContent=css;h.appendChild(s);
var inp=Tag('input');inp.type="text";inp.id='inp';inp.style.display='none';ElT('body').appendChild(inp);
var focus_sb=null;

function Stop(e){if(e.preventDefault)e.preventDefault();if(e.stopPropagation)e.stopPropagation();e.cancelBubble=true;return false}
function ctext(txt,cls){ var n = D.createElement('div'); n.className=cls; n.appendChild(D.createTextNode(txt)); return n; }

function navTo(e){
 setTimeout(function(){
  var n=+W.location.hash.substring(2);
  if (!n){ if(e) n=1; else return }
  console.log("Show: S"+n); Hide('S'+(n-1));Hide('S'+(n+1));Show('S'+n)
 },1);
}
W.addEventListener("hashchange",navTo);navTo();

function new_sbox(sb) {
 var cr = Tag('div','sbcr'), co = Tag('div','scode');
 co.role='log'; co.ariaLive='assertive'; co.ariaLabel='Scratch pad';
 cr.appendChild(ctext('»','CC')); co.tabIndex = -1;
 sb.appendChild(cr); sb.appendChild(co);
 var sbox = { sb, cr, co, lines:0, G:new_gctx() }
 sb.johnnySBox = sbox;
 return sbox;
}

function keydown(e) {
 var sbox = focus_sb
 if (e.which === 13 && sbox) {
  var txt = inp.value, sb = sbox.sb, co = sbox.co, cr = sbox.cr;
  co.appendChild(ctext(txt,'C')); sbox.lines++; // line of input.
  var n,i,o,s=exec_line(txt, sbox.G);
  if (s) { // any output?
   for (i=0,o=s.replace(/\n$/,'').split('\n');i<o.length;i++) {
    co.appendChild(ctext(o[i],'R')); sbox.lines++; // line of output.
    cr.appendChild(ctext("•",'RR'));
   }
  }
  cr.appendChild(ctext("»",'CC')); // next prompt. Math.min(n+1,8)
  n = sbox.lines; n = Math.max(n+1,4); sb.style.height=(2+n*24)+'px'; // grow height.
  focusEd(sbox);
  return Stop(e);
 }
}

function click(e) {
 var el=e.target,s,n;
 while (el) {
  s = el.getAttribute('href');
  if (s) {n=+s.substring(2);if(n){Hide('S'+(n-1));Hide('S'+(n+1));Show('S'+n);return}}
  if (el.johnnySBox) {focusEd(el.johnnySBox);return Stop(e);}
  el = el.parentElement;
 }
 inp.style.display='none'; focus_sb=null; // clear input focus.
}

function focusEd(sbox) {
 focus_sb = sbox;
 sbox.co.appendChild(inp);
 inp.style.left='0px';
 inp.style.top=(sbox.lines*24)+'px';
 inp.style.display='block';
 inp.value='';
 inp.focus();
}

var sboxes = D.querySelectorAll('div.sbox');
for (var i=0;i<sboxes.length;i++) new_sbox(sboxes[i]);
D.addEventListener('click', click, false);
inp.addEventListener('keydown', keydown, false);

}return JBrt();//try{JBrt()}catch(e){console.log(e);Show('JBerr')}
})(document,window);
