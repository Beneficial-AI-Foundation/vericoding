// line contém uma string de tamanho l
// remover p caracteres a partir da posição at

// <vc-helpers>
lemma ArrayCopyLemma(a: array<char>, src: nat, dst: nat, len: nat, oldValues: seq<char>)
  requires src + len <= a.Length
  requires dst + len <= a.Length
  requires oldValues == a[..]
  ensures forall i {:trigger a[dst + i]} :: 0 <= i < len ==> a[dst + i] == oldValues[src + i]
  ensures forall i :: 0 <= i < dst ==> a[i] == oldValues[i]
  ensures forall i :: dst + len <= i < a.Length ==> a[i] == oldValues[i]
{
}

lemma SliceEquivalenceLemma(line: array<char>, at: nat, p: nat, l: nat, i: nat, oldLine: seq<char>)
  requires at + p <= l
  requires l <= line.Length
  requires 0 <= i <= l - p - at
  requires forall j :: 0 <= j < i ==> line[at + j] == oldLine[at + p + j]
  ensures forall j :: 0 <= j < i ==> line[at + j] == oldLine[at + p + j]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Delete(line:array<char>, l:nat, at:nat, p:nat)
  requires l <= line.Length
  requires at+p <= l
  modifies line
  ensures line[..at] == old(line[..at])
  ensures line[at..l-p] == old(line[at+p..l])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  ghost var oldLine := line[..];
  var i := 0;
  while i < l - p - at
    invariant 0 <= i <= l - p - at
    invariant line[..at] == oldLine[..at]
    invariant forall j {:trigger line[at + j]} :: 0 <= j < i ==> line[at + j] == oldLine[at + p + j]
    invariant forall j :: at + i <= j < line.Length ==> line[j] == oldLine[j]
  {
    line[at + i] := line[at + p + i];
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < l - p - at ==> line[at + j] == oldLine[at + p + j];
  assert line[at..l-p] == oldLine[at+p..l];
}
// </vc-code>
