function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
lemma tri_values()
  ensures tri(1) == 3
  ensures tri(2) == 2
  ensures tri(3) == 8
  ensures tri(4) == 3
{
}

lemma tri_sequence_properties(n: nat)
  ensures n >= 1 ==> tri(n) >= 1
{
  if n == 1 {
  } else if n % 2 == 0 {
    assert tri(n) == 1 + n / 2;
    assert n >= 2;
    assert n / 2 >= 1;
  } else if n >= 3 {
    tri_sequence_properties(n - 1);
    tri_sequence_properties(n - 2);
    tri_sequence_properties(n + 1);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def tri(n: int) -> List[int]
Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in the last couple centuries. However, what people don't know is Tribonacci sequence. Tribonacci sequence is defined by the recurrence: tri(1) = 3 tri(n) = 1 + n / 2, if n is even. tri(n) =  tri(n - 1) + tri(n - 2) + tri(n + 1), if n is odd. For example: tri(2) = 1 + (2 / 2) = 2 tri(4) = 3 tri(3) = tri(2) + tri(1) + tri(4) = 2 + 3 + 3 = 8 You are given a non-negative integer number n, you have to a return a list of the first n + 1 numbers of the Tribonacci sequence.
*/
// </vc-description>

// <vc-spec>
method tribonacci_sequence(n: nat) returns (result: seq<nat>)
  requires n >= 0
  ensures |result| == n + 1
  ensures forall i :: 0 <= i <= n ==> result[i] == tri(i + 1)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 1;
  
  while i <= n + 1
    invariant 1 <= i <= n + 2
    invariant |result| == i - 1
    invariant forall j :: 0 <= j < i - 1 ==> result[j] == tri(j + 1)
  {
    tri_sequence_properties(i);
    result := result + [tri(i)];
    i := i + 1;
  }
}
// </vc-code>
