// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): switched to pure function syntax for Min to satisfy compiler */
function Min(a: int, b: int): int {
  if a < b then a else b
}

lemma MinLeLeft(a: int, b: int)
  ensures Min(a, b) <= a
{
  if a < b {
    assert Min(a, b) == a;
  } else {
    assert Min(a, b) == b;
    assert b <= a;
  }
}

lemma MinLeRight(a: int, b: int)
  ensures Min(a, b) <= b
{
  if a < b {
    assert Min(a, b) == a;
    assert a <= b;
  } else {
    assert Min(a, b) == b;
  }
}

lemma MinIsOneOf(a: int, b: int)
  ensures Min(a, b) == a || Min(a, b) == b
{
  if a < b {
    assert Min(a, b) == a;
  } else {
    assert Min(a, b) == b;
  }
}
// </vc-helpers>

// <vc-spec>
method LongestCommonPrefix(str1: array<char>, str2: array<char>) returns (result: array<char>)
    ensures
        result.Length <= str1.Length &&
        result.Length <= str2.Length &&
        (forall i :: 0 <= i < result.Length ==> result[i] == str1[i] && result[i] == str2[i]) &&
        (result.Length == str1.Length || result.Length == str2.Length || 
            (result.Length < str1.Length && result.Length < str2.Length && str1[result.Length] != str2[result.Length]))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented longest common prefix computation and copying using Min helpers */
  var len1 := str1.Length;
  var len2 := str2.Length;
  var m := Min(len1, len2);
  // Establish bounds for m
  MinLeLeft(len1, len2);
  MinLeRight(len1, len2);
  assert m <= len1 && m <= len2;

  var i := 0;
  while i < m && str1[i] == str2[i]
    invariant 0 <= i <= m
    invariant m <= len1 && m <= len2
    invariant forall k :: 0 <= k < i ==> str1[k] == str2[k]
    decreases m - i
  {
    i := i + 1;
  }

  result := new char[i];
  var j := 0;
  while j < i
    invariant 0 <= j <= i
    invariant i <= m
    invariant m <= len1 && m <= len2
    invariant forall k :: 0 <= k < j ==> result[k] == str1[k]
    decreases i - j
  {
    result[j] := str1[j];
    j := j + 1;
  }

  assert j == i;
  assert forall k :: 0 <= k < i ==> result[k] == str1[k];
  assert forall k :: 0 <= k < i ==> str1[k] == str2[k];
  assert forall k :: 0 <= k < i ==> result[k] == str1[k] && result[k] == str2[k];

  if i == m {
    MinIsOneOf(len1, len2);
    assert m == len1 || m == len2;
    assert i == len1 || i == len2;
  } else {
    assert i <= m;
    assert i < m;
    assert i < len1 && i < len2;
    assert !(i < m && str1[i] == str2[i]);
    assert str1[i] != str2[i];
  }
}
// </vc-code>
