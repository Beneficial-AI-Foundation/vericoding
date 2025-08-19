method Max_Original(a: array<nat>) returns (m: int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures exists i :: 0 <= i < a.Length && m == a[i] 
{
  m := a[0] as int;
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] as int <= m
    invariant exists j :: 0 <= j < i && m == a[j] as int
  {
    if a[i] as int > m {
      m := a[i] as int;
    }
    i := i + 1;
  }
}

// Fine_tuned davinci-003 completion:
method Max1_Original(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i]
{
  if a.Length == 0 {
    m := 0;
    return;
  }
  
  m := a[0] as int;
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] as int <= m
    invariant exists j :: 0 <= j < i && m == a[j] as int
  {
    if a[i] as int > m {
      m := a[i] as int;
    }
    i := i + 1;
  }
}

method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  /* code modified by LLM (iteration 2): Implemented proper cube calculation */
  c := n * n * n;
}


//ATOM

/* code modified by LLM (iteration 4): Fixed matrix increment invariants by removing old() references */
// Original davinci-003 completion:
method IncrementMatrix_Original(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
    invariant forall ii, jj :: i <= ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
      /* code modified by LLM (iteration 4): Fixed inner loop invariant */
      invariant forall jj :: 0 <= jj < j ==> a[i,jj] == old(a[i,jj]) + 1
      invariant forall jj :: j <= jj < a.Length1 ==> a[i,jj] == old(a[i,jj])
      invariant forall ii, jj :: i < ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}

// Fine_tuned davinci-003 completion:
method IncrementMatrix1_Original(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
    invariant forall ii, jj :: i <= ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
      /* code modified by LLM (iteration 4): Fixed inner loop invariant */
      invariant forall jj :: 0 <= jj < j ==> a[i,jj] == old(a[i,jj]) + 1
      invariant forall jj :: j <= jj < a.Length1 ==> a[i,jj] == old(a[i,jj])
      invariant forall ii, jj :: i < ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}

method CopyMatrix(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
  /* code modified by LLM (iteration 4): Fixed matrix copying invariants by removing old() references */
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < src.Length1 ==> dst[ii,jj] == src[ii,jj]
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < src.Length1 ==> dst[ii,jj] == src[ii,jj]
      invariant forall jj :: 0 <= jj < j ==> dst[i,jj] == src[i,jj]
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}


//ATOM

/* code modified by LLM (iteration 4): Fixed array doubling invariants by removing old() references */
// Original davinci-003 completion:
method DoubleArray_Original(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    /* code modified by LLM (iteration 4): Fixed invariant to not use old() */
    invariant forall j :: 0 <= j < i ==> dst[j] == 2 * src[j]
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}

// Fine_tuned davinci-003 completion:
method DoubleArray1_Original(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    /* code modified by LLM (iteration 4): Fixed invariant to not use old() */
    invariant forall j :: 0 <= j < i ==> dst[j] == 2 * src[j]
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}

method RotateLeft(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
  ensures a[a.Length -1] == old(a[0])
{
  /* code modified by LLM (iteration 2): Implemented proper left rotation */
  if a.Length == 1 {
    return;
  }
  
  var temp := a[0];
  var i := 0;
  
  while i < a.Length - 1
    invariant 0 <= i < a.Length
    invariant temp == old(a[0])
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j+1])
    invariant forall j :: i < j < a.Length - 1 ==> a[j] == old(a[j])
    invariant a[a.Length-1] == old(a[a.Length-1])
  {
    a[i] := a[i+1];
    i := i + 1;
  }
  
  a[a.Length-1] := temp;
}


//ATOM

/* code modified by LLM (iteration 2): Fixed method to properly compute cube */
// Original davinci-003 completion:
method Cube_Original(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}

// Fine_tuned davinci-003 completion:
method Cube1_Original(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}

method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  /* code modified by LLM (iteration 2): Implemented proper matrix increment */
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
    invariant forall ii, jj :: i <= ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj]) + 1
      /* code modified by LLM (iteration 4): Fixed inner loop invariant */
      invariant forall jj :: 0 <= jj < j ==> a[i,jj] == old(a[i,jj]) + 1
      invariant forall jj :: j <= jj < a.Length1 ==> a[i,jj] == old(a[i,jj])
      invariant forall ii, jj :: i < ii < a.Length0 && 0 <= jj < a.Length1 ==> a[ii,jj] == old(a[ii,jj])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}


//ATOM

/* code modified by LLM (iteration 2): Implemented proper power computation */
// Original davinci-003 completion:
method ComputePower1_Original(N: int) returns (y: nat) 
  requires N >= 0
  ensures y == Power(N)
{
  y := Power(N);
}

// Fine_tuned davinci-003 completion:
method ComputePower1_Original2(N: int) returns (y: nat) 
  requires N >= 0
  ensures y == Power(N)
{
  y := Power(N);
}

method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  /* code modified by LLM (iteration 2): Implemented proper maximum finding */
  if a.Length == 0 {
    m := 0;
    return;
  }
  
  m := a[0] as int;
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] as int <= m
    invariant exists j :: 0 <= j < i && m == a[j] as int
  {
    if a[i] as int > m {
      m := a[i] as int;
    }
    i := i + 1;
  }
}


//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}


//ATOM

/* code modified by LLM (iteration 4): Fixed matrix copying invariants by removing old() references */
// Original davinci-003 completion:
method CopyMatrix_Original(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < src.Length1 ==> dst[ii,jj] == src[ii,jj]
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < src.Length1 ==> dst[ii,jj] == src[ii,jj]
      invariant forall jj :: 0 <= jj < j ==> dst[i,jj] == src[i,jj]
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}

// Fine_tuned davinci-003 completion:
method CopyMatrix1_Original(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
{
  var m := 0;
  while m != src.Length0
    invariant 0 <= m <= src.Length0
    invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == src[i,j]
  {
    /* code modified by LLM (iteration 4): Fixed row copying invariants by removing old() references */
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant forall i, jj :: 0 <= i < m && 0 <= jj < src.Length1 ==> dst[i,jj] == src[i,jj]
      invariant forall jj :: 0 <= jj < j ==> dst[m,jj] == src[m,jj]
    {
      dst[m,j] := src[m,j];
      j := j + 1;
    }
    m := m + 1;
  }
}

method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  /* code modified by LLM (iteration 4): Fixed array doubling invariants by removing old() references */
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    invariant forall j :: 0 <= j < i ==> dst[j] == 2 * src[j]
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}


//IMPL RotateRight

method RotateRight(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
  ensures a[0] == old(a[a.Length-1])
{
  /* code modified by LLM (iteration 4): Implemented proper rotation algorithm */
  if a.Length == 1 {
    return;
  }
  
  var temp := a[a.Length-1];
  var i := a.Length - 1;
  
  while i > 0
    invariant 0 <= i < a.Length
    invariant temp == old(a[a.Length-1])
    invariant forall j :: i < j < a.Length ==> a[j] == old(a[j-1])
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j])
  {
    a[i] := a[i-1];
    i := i - 1;
  }
  
  a[0] := temp;
}