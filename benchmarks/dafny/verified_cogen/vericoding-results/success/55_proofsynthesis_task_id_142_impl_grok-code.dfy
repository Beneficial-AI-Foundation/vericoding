// <vc-preamble>
function CountIdentical(s1: seq<int>, s2: seq<int>, s3: seq<int>): int
    decreases |s1|, |s2|, |s3|
{
    if |s1| == 0 || |s2| == 0 || |s3| == 0 then
        0
    else
        CountIdentical(s1[..|s1|-1], s2[..|s2|-1], s3[..|s3|-1]) + if (s1[|s1|-1] == s2[|s2|-1]
            && s2[|s2|-1] == s3[|s3|-1]) then
            1
        else
            0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed syntax by using nested if expressions to avoid statement-based assignments in function body. */
function MinOfThree(a: int, b: int, c: int): int {
  if (a < b) && (a < c) then a else if (b < c) then b else c
}

/* helper modified by LLM (iteration 2): Added lemmas to prove CountIdentical properties for >=0 and upper bound. */
lemma CountIdenticalNonNegative(s1: seq<int>, s2: seq<int>, s3: seq<int>)
  ensures CountIdentical(s1, s2, s3) >= 0
{
  if |s1| == 0 || |s2| == 0 || |s3| == 0 {
  } else {
    CountIdenticalNonNegative(s1[..|s1|-1], s2[..|s2|-1], s3[..|s3|-1]);
  }
}

lemma CountIdenticalBound(s1: seq<int>, s2: seq<int>, s3: seq<int>)
  requires |s1| == |s2| == |s3|
  ensures CountIdentical(s1, s2, s3) <= MinOfThree(|s1|, |s2|, |s3|)
{
  if |s1| == 0 || |s2| == 0 || |s3| == 0 {
  } else {
    CountIdenticalBound(s1[..|s1|-1], s2[..|s2|-1], s3[..|s3|-1]);
    var prefixCount := CountIdentical(s1[..|s1|-1], s2[..|s2|-1], s3[..|s3|-1]);
    assert prefixCount <= MinOfThree(|s1|-1, |s2|-1, |s3|-1);
    var add := if s1[|s1|-1] == s2[|s2|-1] && s2[|s2|-1] == s3[|s3|-1] then 1 else 0;
    assert CountIdentical(s1, s2, s3) == prefixCount + add;
    var n := |s1|;
    assert n == |s2| && n == |s3|;
    assert MinOfThree(n, n, n) == n;
    assert MinOfThree(n-1, n-1, n-1) == n-1;
  }
}
// </vc-helpers>

// <vc-spec>
method CountIdenticalPosition(arr1: array<int>, arr2: array<int>, arr3: array<int>) returns (count: nat)
    requires arr1.Length == arr2.Length && arr2.Length == arr3.Length
    ensures 0 <= count <= arr1.Length
    ensures CountIdentical(arr1[..], arr2[..], arr3[..]) == count
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Maintained implementation as it depends on helper fixes. */
  CountIdenticalNonNegative(arr1[..], arr2[..], arr3[..]);
  CountIdenticalBound(arr1[..], arr2[..], arr3[..]);
  count := CountIdentical(arr1[..], arr2[..], arr3[..]) as nat;
}
// </vc-code>
