// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate isEven(x: int) { x % 2 == 0 }

lemma SumOfEvensIsEven(a: int, b: int) 
  requires isEven(a) && isEven(b)
  ensures isEven(a + b) 
{
}

lemma EvenNumbersSumToAtLeast8(a: int, b: int, c: int, d: int)
  requires isEven(a) && isEven(b) && isEven(c) && isEven(d)
  requires a >= 2 && b >= 2 && c >= 2 && d >= 2
  ensures a + b + c + d >= 8
{
}
// </vc-helpers>

// <vc-spec>
method is_equal_to_sum_even(n: int) returns (b : bool)

  ensures b <==> n % 2 == 0 && n >= 8
// </vc-spec>
// <vc-code>
{
  if n % 2 != 0 || n < 8 {
    b := false;
  } else {
    var a1 := 2;
    var a2 := 2;
    var a3 := 2;
    var a4 := n - 6;
    
    assert a1 + a2 + a3 + a4 == n;
    assert isEven(a1);
    assert isEven(a2);
    assert isEven(a3);
    assert isEven(a4);
    
    b := true;
  }
}
// </vc-code>
