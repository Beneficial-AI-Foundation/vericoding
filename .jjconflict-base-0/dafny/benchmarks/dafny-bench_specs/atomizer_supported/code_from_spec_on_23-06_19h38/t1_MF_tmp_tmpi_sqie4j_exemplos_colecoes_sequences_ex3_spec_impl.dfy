//IMPL 
// line contém uma string de tamanho l
// remover p caracteres a partir da posição at
method Delete(line:array<char>, l:nat, at:nat, p:nat)
  requires l <= line.Length
  requires at+p <= l
  modifies line
  ensures line[..at] == old(line[..at])
  ensures line[at..l-p] == old(line[at+p..l])
{
  var i := at;
  while i < l - p
    /* code modified by LLM (iteration 1): Fixed loop invariants to properly track array state and ensure bounds are respected */
    invariant at <= i <= l - p
    invariant line[..at] == old(line[..at])
    invariant line[at..i] == old(line[at+p..at+p+(i-at)])
    invariant i + p <= l
    invariant line[i+p..l] == old(line[i+p..l])
  {
    line[i] := line[i + p];
    i := i + 1;
  }
}