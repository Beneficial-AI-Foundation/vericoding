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
  assume false;
}
// </vc-code>