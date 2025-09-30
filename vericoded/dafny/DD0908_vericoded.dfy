// line contém uma string de tamanho l
// remover p caracteres a partir da posição at

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Delete(line:array<char>, l:nat, at:nat, p:nat)
  requires l <= line.Length
  requires at+p <= l
  modifies line
  ensures line[..at] == old(line[..at])
  ensures line[at..l-p] == old(line[at+p..l])
// </vc-spec>
// <vc-code>
{
  var i := at;
  while i < l - p
    invariant at <= i <= l - p
    invariant line[..at] == old(line[..at])
    invariant line[at..i] == old(line[at+p..i+p])
    invariant line[i+p..] == old(line[i+p..])
  {
    line[i] := line[i + p];
    i := i + 1;
  }
}
// </vc-code>

