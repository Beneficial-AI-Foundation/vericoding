/* code modified by LLM (iteration 3): Implemented proper logic instead of assume statement */
method Max_Example1(a: array<nat>) returns (m: int)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures exists i :: 0 <= i < a.Length && m == a[i] 
{
  m := a[0] as int;
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant m >= 0
    invariant forall j :: 0 <= j < i ==> a[j] <= m
    invariant exists j :: 0 <= j < i && m == a[j]
  {
    if a[i] > m {
      m := a[i] as int;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 3): Implemented proper logic instead of assume statement */
method Max_Example2(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i]
{
  if a.Length == 0 {
    m := 0;
  } else {
    m := a[0] as int;
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant m >= 0
      invariant forall j :: 0 <= j < i ==> a[j] <= m
      invariant exists j :: 0 <= j < i && m == a[j]
    {
      if a[i] > m {
        m := a[i] as int;
      }
      i := i + 1;
    }
  }
}

/* code modified by LLM (iteration 3): Implemented proper logic instead of assume statement */
method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}


//ATOM

/* code modified by LLM (iteration 3): Fixed quantifier triggers and invariants for proper matrix copying */
method IncrementMatrix_Example1(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    invariant forall i', j {:trigger dst[i',j]} :: 0 <= i' < i && 0 <= j < src.Length1 ==> dst[i',j] == old(src[i',j])
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant forall i', j' {:trigger dst[i',j']} :: 0 <= i' < i && 0 <= j' < src.Length1 ==> dst[i',j'] == old(src[i',j'])
      invariant forall j' {:trigger dst[i,j']} :: 0 <= j' < j ==> dst[i,j'] == old(src[i,j'])
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 3): Fixed quantifier triggers and invariants for proper matrix copying */
method IncrementMatrix_Example2(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    invariant forall i', j {:trigger dst[i',j]} :: 0 <= i' < i && 0 <= j < src.Length1 ==> dst[i',j] == old(src[i',j])
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant forall i', j' {:trigger dst[i',j']} :: 0 <= i' < i && 0 <= j' < src.Length1 ==> dst[i',j'] == old(src[i',j'])
      invariant forall j' {:trigger dst[i,j']} :: 0 <= j' < j ==> dst[i,j'] == old(src[i,j'])
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}

/* code modified by LLM (iteration 3): Fixed quantifier triggers and invariants for proper matrix copying */
method CopyMatrix(src: array2<int>, dst: array2<int>)
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{
  var i := 0;
  while i < src.Length0
    invariant 0 <= i <= src.Length0
    invariant forall i', j {:trigger dst[i',j]} :: 0 <= i' < i && 0 <= j < src.Length1 ==> dst[i',j] == old(src[i',j])
  {
    var j := 0;
    while j < src.Length1
      invariant 0 <= j <= src.Length1
      invariant forall i', j' {:trigger dst[i',j']} :: 0 <= i' < i && 0 <= j' < src.Length1 ==> dst[i',j'] == old(src[i',j'])
      invariant forall j' {:trigger dst[i,j']} :: 0 <= j' < j ==> dst[i,j'] == old(src[i,j'])
    {
      dst[i,j] := src[i,j];
      j := j + 1;
    }
    i := i + 1;
  }
}


//ATOM

/* code modified by LLM (iteration 3): Implemented proper logic instead of assume statement */
method Cube_Example1(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}

/* code modified by LLM (iteration 3): Implemented proper logic instead of assume statement */
method Cube_Example2(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  c := n * n * n;
}

/* code modified by LLM (iteration 3): Fixed quantifier triggers and invariants for proper matrix increment */
method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall i', j {:trigger a[i',j]} :: 0 <= i' < i && 0 <= j < a.Length1 ==> a[i',j] == old(a[i',j]) + 1
    invariant forall i', j {:trigger a[i',j]} :: i <= i' < a.Length0 && 0 <= j < a.Length1 ==> a[i',j] == old(a[i',j])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall i', j' {:trigger a[i',j']} :: 0 <= i' < i && 0 <= j' < a.Length1 ==> a[i',j'] == old(a[i',j']) + 1
      invariant forall j' {:trigger a[i,j']} :: 0 <= j' < j ==> a[i,j'] == old(a[i,j']) + 1
      invariant forall j' {:trigger a[i,j']} :: j <= j' < a.Length1 ==> a[i,j'] == old(a[i,j'])
      invariant forall i', j' {:trigger a[i',j']} :: i + 1 <= i' < a.Length0 && 0 <= j' < a.Length1 ==> a[i',j'] == old(a[i',j'])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}


//ATOM

/* code modified by LLM (iteration 3): Implemented proper logic instead of assume statement */
method ComputePower_Example1(N: int, a: array<nat>) returns (m: nat) 
  requires N >= 0
  ensures m >= 0
{
  m := 0;
  if a.Length > 0 {
    m := a[0];
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> a[j] <= m
      invariant exists j :: 0 <= j < i && m == a[j]
    {
      if a[i] > m {
        m := a[i];
      }
      i := i + 1;
    }
  }
}

/* code modified by LLM (iteration 3): Implemented proper logic instead of assume statement */
method ComputePower_Example2(N: int, a: array<nat>) returns (m: nat) 
  requires N >= 0
  ensures m >= 0
{
  m := 0;
  if a.Length > 0 {
    m := a[0];
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> a[j] <= m
      invariant exists j :: 0 <= j < i && m == a[j]
    {
      if a[i] > m {
        m := a[i];
      }
      i := i + 1;
    }
  }
}

/* code modified by LLM (iteration 3): Implemented proper logic instead of assume statement */
method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  if a.Length == 0 {
    m := 0;
  } else {
    m := a[0] as int;
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant m >= 0
      invariant forall j :: 0 <= j < i ==> a[j] <= m
      invariant exists j :: 0 <= j < i && m == a[j]
    {
      if a[i] > m {
        m := a[i] as int;
      }
      i := i + 1;
    }
  }
}


//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}


//ATOM

/* code modified by LLM (iteration 3): Fixed invariants and added proper array doubling logic */
method CopyMatrix_Example1(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    invariant forall j {:trigger dst[j]} :: 0 <= j < i ==> dst[j] == 2 * old(src[j])
    invariant forall j {:trigger dst[j]} :: i <= j < src.Length ==> dst[j] == old(dst[j])
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}

/* code modified by LLM (iteration 3): Fixed invariants and added proper array doubling logic */
method CopyMatrix_Example2(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    invariant forall j {:trigger dst[j]} :: 0 <= j < i ==> dst[j] == 2 * old(src[j])
    invariant forall j {:trigger dst[j]} :: i <= j < src.Length ==> dst[j] == old(dst[j])
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}

/* code modified by LLM (iteration 3): Fixed invariants and added proper array doubling logic */
method DoubleArray(src: array<int>, dst: array<int>)
  requires src.Length == dst.Length
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
  var i := 0;
  while i < src.Length
    invariant 0 <= i <= src.Length
    invariant forall j {:trigger dst[j]} :: 0 <= j < i ==> dst[j] == 2 * old(src[j])
    invariant forall j {:trigger dst[j]} :: i <= j < src.Length ==> dst[j] == old(dst[j])
  {
    dst[i] := 2 * src[i];
    i := i + 1;
  }
}


//IMPL RotateLeft

/* code modified by LLM (iteration 4): Fixed invariants to use correct array references for 1D array rotation */
method RotateLeft(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
  ensures a[a.Length -1] == old(a[0])
{
  if a.Length == 1 {
    return;
  }
  
  var temp := a[0];
  var i := 0;
  
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant temp == old(a[0])
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j + 1])
    invariant forall j :: i <= j < a.Length - 1 ==> a[j] == old(a[j])
    invariant a[a.Length - 1] == old(a[a.Length - 1])
  {
    a[i] := a[i + 1];
    i := i + 1;
  }
  
  a[a.Length - 1] := temp;
}