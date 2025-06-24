//IMPL 
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
{
  var mid := a.Length / 2;
  
  b := new int[mid];
  c := new int[a.Length - mid];
  
  var i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant forall j :: 0 <= j < i ==> b[j] == a[j]
  {
    b[i] := a[i];
    i := i + 1;
  }
  
  i := 0;
  while i < c.Length
    invariant 0 <= i <= c.Length
    invariant forall j :: 0 <= j < i ==> c[j] == a[mid + j]
  {
    c[i] := a[mid + i];
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 2): Fixed sequence equality proof and length constraints */
  // Establish basic length relationships
  assert b.Length == mid;
  assert c.Length == a.Length - mid;
  assert b.Length + c.Length == a.Length;
  
  // Prove element-wise equality for both arrays
  assert forall j :: 0 <= j < b.Length ==> b[j] == a[j];
  assert forall j :: 0 <= j < c.Length ==> c[j] == a[mid + j];
  
  // Prove the sequence concatenation step by step
  assert b[..] == a[0..mid];
  assert c[..] == a[mid..a.Length];
  
  // Key insight: use sequence concatenation lemma
  assert a[0..mid] + a[mid..a.Length] == a[0..a.Length];
  assert a[0..a.Length] == a[..];
  
  // Therefore b[..] + c[..] == a[..]
  calc {
    b[..] + c[..];
    == a[0..mid] + a[mid..a.Length];
    == a[0..a.Length];
    == a[..];
  }
  
  // Prove length constraints for a.Length > 1
  if a.Length > 1 {
    /* code modified by LLM (iteration 2): Added explicit reasoning for division properties */
    // When a.Length > 1, we have mid = a.Length / 2
    // This means 0 <= mid < a.Length (integer division)
    assert mid >= 0;
    assert mid == a.Length / 2;
    // For integer division: a.Length / 2 < a.Length when a.Length > 1
    assert mid < a.Length;
    assert b.Length == mid < a.Length;
    
    // For c.Length: c.Length = a.Length - mid
    // Since mid >= a.Length / 2 and a.Length > 1, we have mid >= 1
    // But we need to be more careful about the upper bound
    assert mid <= a.Length / 2; // This is not always true due to integer division
    
    // Better approach: when a.Length > 1, mid is at most a.Length - 1
    // because mid = a.Length / 2 and integer division truncates
    if a.Length == 2 {
      assert mid == 1;
      assert c.Length == 1;
      assert c.Length < a.Length;
    } else if a.Length > 2 {
      assert mid >= 1; // a.Length / 2 >= 1 when a.Length >= 2
      assert mid <= (a.Length - 1); // integer division property
      assert c.Length == a.Length - mid >= a.Length - (a.Length - 1) == 1;
      assert c.Length == a.Length - mid < a.Length; // since mid >= 1
    }
    
    assert c.Length < a.Length;
  }
}