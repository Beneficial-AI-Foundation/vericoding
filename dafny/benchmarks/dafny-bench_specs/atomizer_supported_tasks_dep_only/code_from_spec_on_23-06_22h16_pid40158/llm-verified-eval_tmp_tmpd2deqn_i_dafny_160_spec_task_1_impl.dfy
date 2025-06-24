//ATOM 
function pow(base: int, exponent: int): int
  requires exponent >= 0
  decreases exponent
{
  if exponent == 0 then 1
  else if exponent % 2 == 0 then pow(base * base, exponent / 2)
  else base * pow(base, exponent - 1)
}

//IMPL do_algebra
/* code modified by LLM (iteration 3): Added proper method specification and fixed verification issues */
method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{
  result := operands[0];
  
  var i := 0;
  /* code modified by LLM (iteration 3): Enhanced loop invariants to ensure bounds safety */
  while i < |operators|
    invariant 0 <= i <= |operators|
    invariant |operators| + 1 == |operands|
    invariant operators != [] && operands != []
    invariant |operators| >= 1 && |operands| >= 2
    invariant forall j :: 0 <= j < |operands| ==> operands[j] >= 0
  {
    var op := operators[i];
    var operand := operands[i + 1];
    
    /* code modified by LLM (iteration 3): Added bounds check assertion and improved operator handling */
    assert 0 <= i < |operators|;
    assert 0 <= i + 1 < |operands|;
    
    if op == '+' {
      result := result + operand;
    } else if op == '-' {
      result := result - operand;
    } else if op == '*' {
      result := result * operand;
    } else if op == '/' {
      if operand != 0 {
        result := result / operand;
      } else {
        result := 0; // Handle division by zero
      }
    } else if op == '%' {
      if operand != 0 {
        result := result % operand;
      } else {
        result := 0; // Handle modulo by zero
      }
    } else if op == '^' {
      if operand >= 0 {
        /* code modified by LLM (iteration 3): Added assertion to help verification of pow precondition */
        assert operand >= 0;
        result := pow(result, operand);
      } else {
        result := 0; // Handle negative exponent
      }
    }
    
    i := i + 1;
  }
}