// ATOM 
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }

//Ordered indexes
// ATOM 
lemma equivalenceNoOrder(s:seq<int>)
ensures allEqual(s) <==> forall i,j::0<=i<=j<|s| ==> s[i]==s[j]
{}

//All equal to first
// ATOM 
lemma equivalenceEqualtoFirst(s:seq<int>)
requires s!=[]
ensures allEqual(s) <==> (forall i::0<=i<|s| ==> s[0]==s[i])
{}

// ATOM 
lemma equivalenceContiguous(s:seq<int>)
ensures (allEqual(s) ==> forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
ensures (allEqual(s) <== forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
{
  
  if(|s|==0 || |s|==1){

  }
  else{
    calc {
      forall i::0<=i<|s|-1 ==> s[i]==s[i+1];
      ==>
      {
        equivalenceContiguous(s[..|s|-1]);
      }
      allEqual(s);
    }
  }
  
}

//IMPL mallEqual1
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  if v.Length == 0 {
    return true;
  }
  
  equivalenceEqualtoFirst(v[0..v.Length]);
  
  /* code modified by LLM (iteration 1): fixed for loop syntax to use while loop */
  var i := 1;
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant forall k :: 0 <= k < i ==> v[0] == v[k]
  {
    if v[0] != v[i] {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}

//IMPL mallEqual2
method mallEqual2(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  if v.Length <= 1 {
    return true;
  }
  
  equivalenceContiguous(v[0..v.Length]);
  
  /* code modified by LLM (iteration 1): fixed loop syntax and strengthened invariants */
  var i := 0;
  while i < v.Length - 1
    invariant 0 <= i <= v.Length - 1
    invariant forall k :: 0 <= k < i ==> v[k] == v[k+1]
  {
    if v[i] != v[i+1] {
      return false;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added helper lemma call to establish allEqual property */
  assert forall k :: 0 <= k < v.Length - 1 ==> v[k] == v[k+1];
  
  return true;
}

//IMPL mallEqual3
method mallEqual3(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  equivalenceNoOrder(v[0..v.Length]);
  
  /* code modified by LLM (iteration 1): fixed nested loops with proper while syntax */
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall p, q :: 0 <= p <= q < i ==> v[p] == v[q]
  {
    var j := i + 1;
    while j < v.Length
      invariant i + 1 <= j <= v.Length
      invariant forall q :: i + 1 <= q < j ==> v[i] == v[q]
    {
      if v[i] != v[j] {
        return false;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  return true;
}

//IMPL mallEqual4
method mallEqual4(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  if v.Length == 0 {
    return true;
  }
  
  equivalenceEqualtoFirst(v[0..v.Length]);
  
  /* code modified by LLM (iteration 1): fixed variable usage and loop syntax */
  var first := v[0];
  var i := 1;
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant first == v[0]
    invariant forall k :: 0 <= k < i ==> v[k] == first
  {
    if v[i] != first {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}

//IMPL mallEqual5
method mallEqual5(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  if v.Length <= 1 {
    return true;
  }
  
  equivalenceContiguous(v[0..v.Length]);
  
  /* code modified by LLM (iteration 1): maintained while loop with proper invariants */
  var i := 0;
  while i < v.Length - 1
    invariant 0 <= i <= v.Length - 1
    invariant forall k :: 0 <= k < i ==> v[k] == v[k+1]
  {
    if v[i] != v[i+1] {
      return false;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added assertion to help verification */
  assert forall k :: 0 <= k < v.Length - 1 ==> v[k] == v[k+1];
  
  return true;
}