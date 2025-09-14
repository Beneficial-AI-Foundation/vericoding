predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes

//All equal to first

// <vc-helpers>
lemma allEqualEquivalent(s:seq<int>)
  ensures allEqual(s) <==> (forall i :: 0<=i<|s|-1 ==> s[i]==s[i+1])
{
  if allEqual(s) {
    forall i | 0 <= i < |s|-1
      ensures s[i] == s[i+1]
    {
      assert s[i] == s[i+1];
    }
  }
  if (forall i :: 0<=i<|s|-1 ==> s[i]==s[i+1]) {
    assert allEqual(s) by {
      forall i,j | 0 <= i < |s| && 0 <= j < |s|
        ensures s[i] == s[j]
      {
        if i == j {
          // trivial
        } else if i < j {
          var k := i;
          while k < j
            invariant 0 <= i <= k <= j < |s| && s[i] == s[k]
          {
            assert s[k] == s[k+1];
            k := k + 1;
          }
        } else {
          var k := j;
          while k < i
            invariant 0 <= j <= k <= i < |s| && s[j] == s[k]
          {
            assert s[k] == s[k+1];
            k := k + 1;
          }
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  if v.Length == 0 {
    return true;
  }
  var i := 0;
  while i < v.Length - 1
  invariant 0 <= i < v.Length
  invariant forall k :: 0 <= k <= i ==> v[k] == v[0]
  {
    if v[i] != v[i+1] {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

