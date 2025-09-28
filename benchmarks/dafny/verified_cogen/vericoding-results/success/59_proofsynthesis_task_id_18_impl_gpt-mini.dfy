// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): checks whether a char is present in an array */
function InArray(a: array<char>, c: char): bool reads a { c in a[..] }
// </vc-helpers>

// <vc-spec>
method RemoveChars(str1: array<char>, str2: array<char>) returns (result: array<char>)
    ensures
        forall i :: 0 <= i < result.Length ==> (result[i] in str1[..] && result[i] !in str2[..])
    ensures
        forall i :: 0 <= i < str1.Length ==> (str1[i] in str2[..] || str1[i] in result[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build sequence of chars from str1 excluding those in str2 and return array */
  var resSeq: seq<char> := [];
  var i := 0;
  while i < str1.Length
    invariant 0 <= i <= str1.Length
    invariant forall idx :: 0 <= idx < i ==> (str1[idx] in str2[..] || str1[idx] in resSeq[..])
    invariant forall p :: 0 <= p < |resSeq| ==> (resSeq[p] in str1[..] && !(resSeq[p] in str2[..]))
  {
    if !(str1[i] in str2[..]) {
      resSeq := resSeq + [str1[i]];
    }
    i := i + 1;
  }

  result := new char[|resSeq|];
  var j := 0;
  while j < |resSeq|
    invariant 0 <= j <= |resSeq|
    invariant forall t :: 0 <= t < j ==> result[t] == resSeq[t]
  {
    result[j] := resSeq[j];
    j := j + 1;
  }
}

// </vc-code>
