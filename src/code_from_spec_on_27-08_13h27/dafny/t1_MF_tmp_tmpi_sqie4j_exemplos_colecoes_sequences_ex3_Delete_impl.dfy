// line contém uma string de tamanho l
// remover p caracteres a partir da posição at

// <vc-helpers>
lemma ShiftPreservesContent(line: array<char>, l: nat, at: nat, p: nat, i: nat)
  requires l <= line.Length
  requires at + p <= l
  requires at <= i < l - p
  ensures line[i] == line[i + p]
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
method DeleteImpl(line: array<char>, l: nat, at: nat, p: nat)
  requires l <= line.Length
  requires at + p <= l
  modifies line
  ensures line[..at] == old(line[..at])
  ensures line[at..l-p] == old(line[at+p..l])
{
  var i := at;
  while i < l - p
    invariant at <= i <= l - p
    invariant line[..at] == old(line[..at])
    invariant forall k :: at <= k < i ==> line[k] == old(line[k + p])
    invariant forall k :: i <= k < l - p ==> line[k] == old(line[k + p])
  {
    line[i] := line[i + p];
    i := i + 1;
  }
}
// </vc-code>
