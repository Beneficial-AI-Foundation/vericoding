//IMPL copy
method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]
{
  r := new int[dest.Length];
  
  // Copy the prefix part (before dStart)
  var i := 0;
  while i < dStart
    /* code modified by LLM (iteration 3): added bounds checking invariant */
    invariant 0 <= i <= dStart
    invariant dStart <= dest.Length
    invariant r[..i] == dest[..i]
  {
    r[i] := dest[i];
    i := i + 1;
  }
  
  // Copy from src to dest
  i := 0;
  while i < len
    /* code modified by LLM (iteration 3): added bounds checking invariants */
    invariant 0 <= i <= len
    invariant dStart + len <= dest.Length
    invariant sStart + len <= src.Length
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart..dStart+i] == src[sStart..sStart+i]
  {
    r[dStart + i] := src[sStart + i];
    i := i + 1;
  }
  
  // Copy the suffix part (after dStart + len)
  i := dStart + len;
  while i < dest.Length
    /* code modified by LLM (iteration 3): added bounds checking invariants */
    invariant dStart + len <= i <= dest.Length
    invariant r.Length == dest.Length
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart..dStart+len] == src[sStart..sStart+len]
    invariant r[dStart+len..i] == dest[dStart+len..i]
  {
    r[i] := dest[i];
    i := i + 1;
  }
}