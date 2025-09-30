predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes

//All equal to first

// <vc-helpers>
lemma allEqualEmpty()
  ensures allEqual([])
{
}

lemma allEqualSingleton(x: int)
  ensures allEqual([x])
{
}

lemma allEqualImpliesPrefix(s: seq<int>, k: nat)
  requires k <= |s|
  requires allEqual(s)
  ensures allEqual(s[0..k])
{
}

lemma prefixAllEqualExtend(s: seq<int>, k: nat)
  requires 0 < k < |s|
  requires allEqual(s[0..k])
  requires s[k] == s[0]
  ensures allEqual(s[0..k+1])
{
  var prefix := s[0..k+1];
  forall i, j | 0 <= i < |prefix| && 0 <= j < |prefix|
    ensures prefix[i] == prefix[j]
  {
    if i < k && j < k {
      assert prefix[i] == s[i];
      assert prefix[j] == s[j];
      assert s[0..k][i] == s[i];
      assert s[0..k][j] == s[j];
    } else if i == k {
      assert prefix[i] == s[k] == s[0];
      if j < k {
        assert prefix[j] == s[j] == s[0..k][j];
      }
    } else if j == k {
      assert prefix[j] == s[k] == s[0];
      if i < k {
        assert prefix[i] == s[i] == s[0..k][i];
      }
    }
  }
}

lemma notAllEqualWitness(s: seq<int>, i: nat)
  requires i < |s|
  requires |s| > 0
  requires s[i] != s[0]
  ensures !allEqual(s)
{
  assert 0 < |s| && i < |s| && s[0] != s[i];
}
// </vc-helpers>

// <vc-spec>
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  if v.Length == 0 {
    b := true;
    allEqualEmpty();
  } else if v.Length == 1 {
    b := true;
    allEqualSingleton(v[0]);
  } else {
    var i := 1;
    b := true;
    
    while i < v.Length
      invariant 1 <= i <= v.Length
      invariant b == allEqual(v[0..i])
    {
      if v[i] != v[0] {
        b := false;
        notAllEqualWitness(v[0..i+1], i);
        assert v[0..i+1][i] == v[i];
        assert v[0..i+1][0] == v[0];
      } else {
        if b {
          prefixAllEqualExtend(v[0..v.Length], i);
        }
      }
      i := i + 1;
    }
    
    assert i == v.Length;
    assert v[0..v.Length] == v[..];
  }
}
// </vc-code>

