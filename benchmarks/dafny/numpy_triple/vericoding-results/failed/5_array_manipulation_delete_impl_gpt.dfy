// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): sequence delete helper to remove element at index */
function dropAt(s: seq<real>, i: nat): seq<real>
  requires |s| > 0
  requires i < |s|
{
  s[..i] + s[i + 1..]
}

/* helper modified by LLM (iteration 4): lemma proving key properties of dropAt (length, element preservation, shift, and existence) */
lemma LemmaDropAtProperties(s: seq<real>, i: nat)
  requires |s| > 0
  requires i < |s|
  ensures |dropAt(s, i)| == |s| - 1
  ensures forall k :: 0 <= k < i ==> dropAt(s, i)[k] == s[k]
  ensures forall k :: i <= k < |dropAt(s, i)| ==> dropAt(s, i)[k] == s[k + 1]
  ensures forall ii :: 0 <= ii < |s| && ii != i ==> exists j :: 0 <= j < |dropAt(s, i)| && dropAt(s, i)[j] == s[ii]
{
  assert dropAt(s, i) == s[..i] + s[i + 1..];
  assert |s[..i]| == i;
  assert |s[i + 1..]| == |s| - (i + 1);
  assert |dropAt(s, i)| == |s[..i]| + |s[i + 1..]|;
  assert |dropAt(s, i)| == |s| - 1;

  // Elements before the deleted index remain the same
  forall k | 0 <= k < i
    ensures dropAt(s, i)[k] == s[k]
  {
    assert dropAt(s, i) == s[..i] + s[i + 1..];
    assert |s[..i]| == i;
    assert k < |s[..i]|;
    assert dropAt(s, i)[k] == s[..i][k];
    assert s[..i][k] == s[k];
  }

  // Elements after the deleted index shift left by one
  forall k | i <= k < |dropAt(s, i)|
    ensures dropAt(s, i)[k] == s[k + 1]
  {
    assert dropAt(s, i) == s[..i] + s[i + 1..];
    assert |s[..i]| == i;
    assert k < |dropAt(s, i)|;
    assert |dropAt(s, i)| == |s[..i]| + |s[i + 1..]|;
    assert |s[..i]| == i;
    assert k < i + |s[i + 1..]|;
    assert 0 <= k - i;
    assert k - i < |s[i + 1..]|;
    assert dropAt(s, i)[k] == s[i + 1..][k - i];
    assert s[i + 1..][k - i] == s[(i + 1) + (k - i)];
    assert (i + 1) + (k - i) == k + 1;
  }

  // Every element except the deleted one appears in the result
  forall ii | 0 <= ii < |s| && ii != i
    ensures exists j :: 0 <= j < |dropAt(s, i)| && dropAt(s, i)[j] == s[ii]
  {
    if ii < i {
      assert dropAt(s, i) == s[..i] + s[i + 1..];
      assert |s[..i]| == i;
      assert ii < |s[..i]|;
      assert dropAt(s, i)[ii] == s[..i][ii];
      assert s[..i][ii] == s[ii];
      assert |dropAt(s, i)| == |s| - 1;
      assert i <= |s| - 1; // from i < |s|
      assert ii < |dropAt(s, i)|;
      assert exists j :: j == ii && 0 <= j < |dropAt(s, i)| && dropAt(s, i)[j] == s[ii];
    } else {
      assert ii >= i + 1; // since ii >= i and ii != i
      var j := ii - 1;
      assert 0 <= j;
      assert dropAt(s, i) == s[..i] + s[i + 1..];
      assert |dropAt(s, i)| == |s| - 1;
      assert j < |dropAt(s, i)|; // ii < |s| => ii - 1 < |s| - 1
      assert |s[..i]| == i;
      assert |s[i + 1..]| == |s| - (i + 1);
      assert i + |s[i + 1..]| == |s| - 1;
      assert j < i + |s[i + 1..]|; // since j < |s| - 1
      assert j >= i; // because ii >= i + 1 => ii - 1 >= i
      assert 0 <= j - i;
      assert j - i < |s[i + 1..]|;
      assert dropAt(s, i)[j] == s[i + 1..][j - i];
      assert s[i + 1..][j - i] == s[(i + 1) + (j - i)];
      assert (i + 1) + (j - i) == j + 1;
      assert j + 1 == ii;
      assert dropAt(s, i)[j] == s[ii];
      assert exists k :: k == j && 0 <= k < |dropAt(s, i)| && dropAt(s, i)[k] == s[ii];
    }
  }
}

// </vc-helpers>

// <vc-spec>
method Delete(arr: seq<real>, index: nat) returns (result: seq<real>)
  // Preconditions: array must be non-empty and index must be valid
  requires |arr| > 0
  requires index < |arr|
  
  // Postcondition: result has exactly one fewer element
  ensures |result| == |arr| - 1
  
  // Postcondition: elements before the deleted index maintain their positions  
  ensures forall i :: 0 <= i < index ==> result[i] == arr[i]
  
  // Postcondition: elements after the deleted index are shifted left by one
  ensures forall i :: index <= i < |result| ==> result[i] == arr[i + 1]
  
  // Postcondition: every element except the deleted one appears in the result
  ensures forall i :: 0 <= i < |arr| && i != index ==> 
    exists j :: 0 <= j < |result| && result[j] == arr[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): compute result via dropAt and discharge postconditions using lemma */
  result := dropAt(arr, index);
  LemmaDropAtProperties(arr, index);
}
// </vc-code>
