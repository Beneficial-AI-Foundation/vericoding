//ATOM 
function pow(base: int, exponent: int): int
  requires exponent >= 0
{
  if exponent == 0 then 1
  else if exponent % 2 == 0 then pow(base * base, exponent / 2)
  else base * pow(base, exponent - 1)
}

//IMPL do_algebra
method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{
  result := operands[0];
  var i := 0;
  
  /* code modified by LLM (iteration 1): enhanced loop invariants for proper verification */
  while i < |operators|
    invariant 0 <= i <= |operators|
    invariant |operators| + 1 == |operands|
    invariant forall j :: 0 <= j < |operands| ==> operands[j] >= 0
    decreases |operators| - i
  {
    /* code modified by LLM (iteration 1): explicit bounds verification before array access */
    assert i < |operators|;
    assert i + 1 < |operands|;
    
    var op := operators[i];
    var operand := operands[i + 1];
    
    /* code modified by LLM (iteration 1): complete algebraic operation handling with proper guards */
    if op == '+' {
      result := result + operand;
    } else if op == '-' {
      result := result - operand;
    } else if op == '*' {
      result := result * operand;
    } else if op == '/' && operand != 0 {
      result := result / operand;
    } else if op == '^' {
      /* code modified by LLM (iteration 1): safe exponentiation with non-negative base check */
      if result >= 0 {
        result := pow(result, operand);
      } else {
        result := 0;
      }
    }
    
    i := i + 1;
  }
}