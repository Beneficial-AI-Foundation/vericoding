function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma CountRecEqualsSet(a: seq<int>, x: int)
  ensures count_rec(a, x) == |set i | 0 <= i < |a| && a[i] == x|
{
  if |a| == 0 {
    // Base case: empty sequence
    calc {
      count_rec(a, x);
      0;
      |set i | 0 <= i < 0 && a[i] == x|;
    }
  } else {
    // Inductive case
    CountRecEqualsSet(a[1..], x);
    calc {
      |set i | 0 <= i < |a| && a[i] == x|
      == // Split set into index 0 and indices > 0
        |set i | 0<=i<|a| && a[i]==x && i==0| + |set i | 0<=i<|a| && a[i]==x && i>=1|;
      == // Evaluate index 0 term
        (if a[0] == x then 1 else 0) + |set i | 0<=i<|a| && a[i]==x && i>=1|;
      == // Shift index: j = i-1
        (if a[0] == x then 1 else 0) + |set j | 0<=j<|a[1..]| && a[j+1]==x|;
      == // Element access via sequence slice
        (if a[0] == x then 1 else 0) + |set j | 0<=j<|a[1..]| && a[1..][j]==x|;
      == // Apply induction hypothesis
        (if a[0] == x then 1 else 0) + count_rec(a[1..], x);
      == // Recursive definition of count_rec
        count_rec(a, x);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
cnt := count_rec(a, x);
CountRecEqualsSet(a, x);
// </vc-code>

