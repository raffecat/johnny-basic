"use strict";

var enc = new TextEncoder(); // utf-8
var dec = new TextDecoder(); // utf-8

var THEN = new Uint8Array([84,116, 72,104, 69,101, 78,110]);
var ELSE = new Uint8Array([69,101, 76,108, 83,115, 69,101]);
var PRINT = new Uint8Array([80,112, 82,114, 73,105, 78,110, 84,116]);
var NEXT  = new Uint8Array([78,110, 69,101, 88,120, 84,116]);

function isAlpha(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122); }
function rest(c,p) { return dec.decode(c.slice(p)); }
function subs(c,s,e) { return dec.decode(c.slice(s,e)); }
function skip_ws(c,p) { while (c[p] === 32) ++p; return p; }

function m_error(c,p,msg) {
  return { $:'error', msg, col:p+1, text:rest(c,p) }
}

// A line is continuously invalid until we can recognise a statement.

function m_stmt(c,p,opt) {
  // m_stmt: attempt to recognise a statement.
  var t, at;
  while (c[p] === 32) ++p; at=p; // skip spaces
  switch (c[p]) {
    case 73: case 105: {           t = c[p+1]; // "I"
      if (t === 70 || t === 102) {             // "F"
        return m_if(c,p+2,at);
      }
    }
    case 80: case 112: { // "P"
      p = is_kw(c,p,PRINT,1)
      if (p) {
        return m_print(c,p,at);
      }
    }
    case 63: { // "?" shorthand for PRINT.
      return m_print(c,p,at);
    }
  }
  if (opt) return null; // no match.
  return m_error(c,p,"Statement expected")
}

function m_print(c,p,at) {
  var t, vals = []
  for (;;) {
    p = skip_ws(c,p);
    switch (c[p]) {
      case 10: case 13: // EOL
      case 58: // ":"
        return { $:'print', at, vals, aft:p }
      case 44: // ","
      case 59: // ";"
      case 39: // "'"
        // ...
        p++;
        continue;
        case 69: case 101: { // "E"
          if (is_kw(c,p,ELSE,2)) {
            // Must exit m_print before ELSE,
            // in case this statement is inside an IF-ELSE.
            return { $:'print', at, vals, aft:p }
          }
        }
    }
    var expr = m_expr(c,p,1)
    if (expr !== null) {
      vals.push(expr); p = expr.aft;
    } else {
      vals.push(m_error(c,p,"Expecting an expression print in PRINT statement"));
      return { $:'print', at, vals, aft:c.length }
    }
  }
}

function m_if(c,p,at) {
  // IF•{expr}THEN{ln-stmt}ELSE{ln-stmt}
  // IF•{expr}{stmt}ELSE{ln-stmt}
  // IF is AMBIGUOUS: it might be part of a var name.
  var cond, then_s, else_s, thn, els, valid = 1;
  cond = m_expr(c,p,1);
  if (cond === null) return m_error(c,p,"Incomplete IF statement");
  thn = is_kw(c, cond.aft, THEN, 2);
  if (thn) {
    // ACCEPT: remainder MUST parse as IF.
    then_s = m_implicit_goto(c, thn);
    if (then_s === null) then_s = m_stmt(c, thn, 1);
    if (then_s === null) {
      then_s = m_error(c,thn,"Statement or Line Number expected after THEN");
      valid = 0;
    }
  } else {
    // Missing THEN, but a Stmt is also allowed.
    then_s = m_stmt(c, cond.aft, 1);
    if (then_s !== null) {
      // ACCEPT: remainder MUST parse as IF.
    } else {
      // Missing Stmt or THEN.
      // DOWNCAST IF•Cond to IFName=Expr, if Cond is a simple assign.
      // ...
      then_s = m_error(c,cond.aft,"Statement or THEN expected after IF condition");
      valid = 0;
    }
  }
  if (valid) {
    // Optional: ELSE {line|stmt}
    els = is_kw(c, then_s.aft, ELSE, 2);
    if (els) {
      else_s = m_implicit_goto(c, els);
      if (else_s === null) else_s = m_stmt(c, els, 1);
      if (else_s === null) {
        else_s = m_error(c,els,"Statement or Line Number expected after ELSE");
      }
    }
  }
  return { $:'if', at, cond, then_s, else_s }
}

function m_implicit_goto(c,p) {
  var num = m_number(c,p,1);
  if (num) {
    // Implicit GoTo (a line number)
    return { $:'goto', at:num.at, line:num.val, aft:num.aft }
  }
  return null;
}

function m_ident(c,p,opt) {
  var at, t = c[p];
  while (t === 32) t = c[++p]; at=p; // skip spaces
  while (isAlpha(t) || t === 95) t=c[++p];
  if (p > at) {
    return { $:'name', at, name:subs(c,at,p), aft:p }
  }
  if (opt) return null; return m_error(c,p,"Name expected");
}

function m_number(c,p,opt) {
  var at, val = 0, t = c[p];
  while (t === 32) { t = c[++p]; }; at=p; // skip spaces
  while (t >= 48 && t <= 57) { val=val*10+(t-48); t=c[++p]; }
  if (p > at) {
    return { $:'num', at, val, aft:p }
  }
  if (opt) return null; return m_error(c,p,"Number expected");
}

function m_string(c,p,opt) {
  var org, at, s = "", t = c[p];
  while (t === 32) t = c[++p]; org=p; // skip spaces
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

function m_expr(c,p,opt) {
  var t, at, right, left = m_nud(c,p)
  if (left !== null) {
    // infix operator loop.
    for (;;) {
      p = left.aft; t = c[p];
      while (t === 32) { t = c[++p]; }; at=p; // skip spaces
      switch (t) {
        case 61: { ++p; // "="
          right = m_expr(c,p,0)
          left = { $:'eq', at, left, right, aft:right.aft }
          break;
        }
        default:
          return left;
      }
    }
  }
  if (opt) return null; return m_error(c,p,"Expression expected");
}

function m_nud(c,p) {
  var at, t = c[p];
  while (t === 32) { t = c[++p]; }; at=p; // skip spaces
  switch (t) {
    case 45: { ++p; // "-"
      var num = m_number(c,p,1);
      if (num !== null) { // Negative Number Literal
        num.val = -num.val;
        return num;
      }
      var right = m_nud(c,p);
      if (right !== null) return { $:'neg', at, right, aft:right.aft }
      return m_error(c,p,"Expression expected after '-' sign");
    }
    case 34: { // '"'
      return m_string(c,p,0);
    }
  }
  var name = m_ident(c,p,1);
  if (name !== null) return name;
  var num = m_number(c,p,1);
  if (num !== null) return num;
  return null;
}

function is_kw(c,p,kw,min) {
  while (c[p] === 32) ++p; // skip spaces
  for (var t, dot = p + min, i = 0; i < kw.length; i += 2) {
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
  var line = enc.encode(text);
  var stmt = m_stmt(line, 0);
  if (stmt !== null) return stmt;
  return m_error(line,0,"Statement expected");
}

console.log(JSON.stringify(m_line('IFA=1PRINT"Y"ELSE40'),null,2));
var zz = 1;
