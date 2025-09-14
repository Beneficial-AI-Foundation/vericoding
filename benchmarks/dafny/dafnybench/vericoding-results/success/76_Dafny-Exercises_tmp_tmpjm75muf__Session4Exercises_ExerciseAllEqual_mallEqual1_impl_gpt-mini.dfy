predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes

//All equal to first

// <vc-helpers>
// (No helper code needed)
// </vc-helpers>

// <vc-spec>
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  if v.Length == 0 {
    b := true;
    return;
  }
  b := true;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant b == (forall p,q :: 0 <= p < i && 0 <= q < i ==> v[p] == v[q])
  {
    b := b && (forall j :: 0 <= j < i ==> v[j] == v[i]);
    i := i + 1;
  }
  assert b == allEqual(v[0..v.Length]);
}
// </vc-code>

