"use strict";

var enc = new TextEncoder(), dec = new TextDecoder(); // utf-8

function kw(caps) { // "THEN" => U8[84,116, 72,104, 69,101, 78,110]
  var i, b = enc.encode(caps), v = new Uint8Array(b.length*2), p=0;
  for (i=0; i<b.length; i++) { v[p++] = b[i]; v[p++] = b[i]+32; } // +32 to lower-case.
  return v;
}

var LET=kw("LET"),DIM=kw("DIM"),THEN=kw("THEN"),ELSE=kw("ELSE"),FOR=kw("FOR"),NEXT=kw("NEXT");
var REPEAT=kw("REPEAT"),WHILE=kw("WHILE"),CASE=kw("CASE"),END=kw("END"),GOTO=kw("GOTO");
var GOSUB=kw("GOSUB"),RETURN=kw("RETURN"),READ=kw("READ"),RESTORE=kw("RESTORE"),SET=kw("SET");
var PRINT=kw("PRINT");

function log(msg,c,p) {
  console.log(`${msg} ${subs(c,p-4,p+5)}\n${'^'.padStart(msg.length+6)}`);
}

function isAlpha(c) { return (c >= 65 && c <= 90) || (c >= 97 && c <= 122); }
function rest(c,p) { return dec.decode(c.slice(p)); }
function subs(c,s,e) { return dec.decode(c.slice(s,e)); }
function skip_ws(c,p) { while (c[p] === 32) ++p; return p; }

function m_error(c,p,msg) {
  p = skip_ws(c,p);
  return { $:'error', msg, col:p+1, text:rest(c,p) }
}

// A line is continuously invalid until we can recognise a statement.

function m_stmt(c,p,opt) {
  // m_stmt: attempt to recognise a statement.
  p = skip_ws(c,p);
  var t, at = p;
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
    case 71: case 103: { // "G"
      p = is_kw(c,p,GOTO,1);
      if (p) {
        return m_goto_line(c,p,"Expecting a line number after GOTO");
      }
    }
  }
  if (opt) return null; // no match.
  return m_error(c,at,"Statement expected")
}

function m_print(c,p,at) {
  var t, vals = []
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
  if (cond === null) return m_error(c,p,"Incomplete IF statement (Condition expected)");
  thn = is_kw(c, cond.aft, THEN, 2);
  if (thn) {
    // ACCEPT: remainder MUST parse as IF.
    then_s = m_goto_line(c, thn, null);
    if (then_s === null) then_s = m_stmt(c, thn, 1);
    if (then_s === null) {
      then_s = m_error(c,thn,"Unrecognised Statement after THEN (Statement expected)");
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
      then_s = m_error(c,cond.aft,"Unrecognised Statement after IF condition (Statement expected)");
      valid = 0;
    }
  }
  if (valid) {
    // Optional: ELSE {line|stmt}
    els = is_kw(c, then_s.aft, ELSE, 2);
    if (els) {
      else_s = m_goto_line(c, els, null);
      if (else_s === null) else_s = m_stmt(c, els, 1);
      if (else_s === null) {
        else_s = m_error(c,els,"Unrecognised Statement after ELSE (Statement expected)");
      }
    }
  }
  return { $:'if', at, cond, then_s, else_s }
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

function m_ident_i(c,p,opt) {
  var at = p, t = c[p];
  while (isAlpha(t) || t === 95) t=c[++p];
  if (p > at) {
    return { $:'name', at, name:subs(c,at,p), aft:p }
  }
  if (opt) return null; return m_error(c,p,"Name expected");
}

function m_number_i(c,p,req) {
  log("num",c,p)
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
  p = skip_ws(c,p);
  var at=p, t = c[p];
  switch (t) {
    case 45: { ++p; // "-"
      var right = m_nud(c,p);
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
  }
  var name = m_ident_i(c,p,1);
  if (name !== null) return name;
  var num = m_number_i(c,p,"");
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

var lines = [
  'IFA=1PRINT"Y"ELSE40',
  'IF A = 1 THEN PRINT "Y" ELSE GOTO 40',
];

for (var zz of lines) {
  console.log(JSON.stringify(m_line(zz),null,2));
}
zz = 1;
