// There's a `pow` function already defined for exponentiation

// The method should evaluate the expression represented by alternating operands and operators. I need to handle operator precedence correctly, with exponentiation having the highest precedence, then multiplication and division, then addition and subtraction.

// <vc-spec>
function pow(base: int, exponent: int): int
  requires exponent >= 0
  decreases exponent
{
  if exponent == 0 then 1
  else if exponent % 2 == 0 then pow(base * base, exponent / 2)
  else base * pow(base, exponent - 1)
}

method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
// </vc-spec>

// <vc-helpers>
method evaluate_expression(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{
  var ops := operators;
  var vals := operands;
  
  // First pass: handle exponentiation (highest precedence)
  var i := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant |ops| + 1 == |vals|
    invariant |ops| <= |operators|
    invariant forall j :: 0 <= j < |vals| ==> vals[j] >= 0
  {
    if ops[i] == '^' {
      var new_val := pow(vals[i], vals[i + 1]);
      vals := vals[..i] + [new_val] + vals[i + 2..];
      ops := ops[..i] + ops[i + 1..];
    } else {
      i := i + 1;
    }
  }
  
  // Second pass: handle multiplication and division
  i := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant |ops| + 1 == |vals|
    invariant |ops| <= |operators|
    invariant forall j :: 0 <= j < |vals| ==> vals[j] >= 0
  {
    if ops[i] == '*' {
      var new_val := vals[i] * vals[i + 1];
      vals := vals[..i] + [new_val] + vals[i + 2..];
      ops := ops[..i] + ops[i + 1..];
    } else if ops[i] == '/' && vals[i + 1] != 0 {
      var new_val := vals[i] / vals[i + 1];
      vals := vals[..i] + [new_val] + vals[i + 2..];
      ops := ops[..i] + ops[i + 1..];
    } else {
      i := i + 1;
    }
  }
  
  // Third pass: handle addition and subtraction
  i := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant |ops| + 1 == |vals|
    invariant |ops| <= |operators|
  {
    if ops[i] == '+' {
      var new_val := vals[i] + vals[i + 1];
      vals := vals[..i] + [new_val] + vals[i + 2..];
      ops := ops[..i] + ops[i + 1..];
    } else if ops[i] == '-' {
      var new_val := vals[i] - vals[i + 1];
      vals := vals[..i] + [new_val] + vals[i + 2..];
      ops := ops[..i] + ops[i + 1..];
    } else {
      i := i + 1;
    }
  }
  
  result := if |vals| > 0 then vals[0] else 0;
}
// </vc-helpers>

// <vc-code>
{
  result := evaluate_expression(operators, operands);
}
// </vc-code>