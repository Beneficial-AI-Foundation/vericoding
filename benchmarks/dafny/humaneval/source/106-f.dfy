function factorial_spec(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * factorial_spec(n - 1)
}
// pure-end
function sum_spec(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n + sum_spec(n - 1)
}
// pure-end
method f(n : int) returns (result : seq<int>)
  // pre-conditions-start
  requires n >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == n
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 == 0 ==> result[i] == factorial_spec(i)
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 != 0 ==> result[i] == sum_spec(i)
  // post-conditions-end
{
  // impl-start
  result := [];
  var i := 0;
  while i < n
    // invariants-start
    invariant i >= 0 && i <= n
    invariant |result| == i
    invariant forall i : int :: i >= 0 && i < |result| && i % 2 == 0 ==> result[i] == factorial_spec(i)
    invariant forall i : int :: i >= 0 && i < |result| && i % 2 != 0 ==> result[i] == sum_spec(i)
    // invariants-end
  {
    if i % 2 == 0 {
      var x := 1;
      var j := 0;
      while j < i
        // invariants-start
        invariant j >= 0 && j <= i
        invariant x == factorial_spec(j)
        // invariants-end
      {
        j := j + 1;
        x := x * j;
      }
      result := result + [x];
    } else {
      var x := 1;
      var j := 0;
      while j < i
        // invariants-start
        invariant j >= 0 && j <= i
        invariant x == sum_spec(j)
        // invariants-end
      {
        j := j + 1;
        x := x + j;
      }
      result := result + [x];
    }
    i := i + 1;
  }
  // impl-end
}
