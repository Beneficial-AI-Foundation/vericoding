OK predicate: invariante da representação abstrata associada à coleção do tipo fila

    Operações
        - OK construtor inicia fila fazia
        - OK adicionar novo elemento na fila -> enfileira()
        - OK remover um elemento da fila e retornar seu valor caso a fila contenha elementos  -> desenfileira()
        - OK verificar se um elemento pertence a fila  -> contem()
        - OK retornar numero de elementos da fila -> tamanho()
        - OK verificar se a fila é vazia ou não -> estaVazia()
        - OK concatenar duas filas retornando uma nova fila sem alterar nenhuma das outras -> concat()

    OK criar método main testando a implementação 
    OK transformar uso de naturais para inteiros
*/

class {:autocontracts}  Fila
    {
  var a: array<int>
  var cauda: nat
  const defaultSize: nat

  ghost var Conteudo: seq<int>

  // invariante
  ghost predicate Valid()  {
                        defaultSize > 0
    && a.Length >= defaultSize
    && 0 <= cauda <= a.Length
    && Conteudo == a[0..cauda]
    }

    // inicia fila com 3 elementos
// <vc-spec>
    constructor ()
      ensures Conteudo == []
      ensures defaultSize == 3
      ensures a.Length == 3
      ensures fresh(a)
    {
    defaultSize := 3;
    a := new int[3];
    cauda := 0;
    Conteudo := [];
    }

  function tamanho():nat
    ensures tamanho() == |Conteudo|
    {
                    cauda
    }

  function estaVazia(): bool
    ensures estaVazia() <==> |Conteudo| == 0
    {
                      cauda == 0
    }

// <vc-helpers>
method resize()
  requires cauda == a.Length
  ensures a.Length == old(a.Length) * 2
  ensures a.Length >= defaultSize
  ensures cauda < a.Length
  ensures Conteudo == old(Conteudo)
  ensures fresh(a)
  modifies this
{
  var oldArray := a;
  var oldConteudo := Conteudo;
  var newArray := new int[a.Length * 2];
  var i := 0;
  while i < cauda
    invariant 0 <= i <= cauda
    invariant cauda <= oldArray.Length
    invariant newArray.Length == oldArray.Length * 2
    invariant forall k :: 0 <= k < i ==> newArray[k] == oldArray[k]
  {
    newArray[i] := oldArray[i];
    i := i + 1;
  }
  a := newArray;
  
  // Prove that the content is preserved
  assert forall k :: 0 <= k < cauda ==> a[k] == oldArray[k];
  assert a[0..cauda] == oldArray[0..cauda];
  assert oldConteudo == oldArray[0..cauda];
  assert a[0..cauda] == oldConteudo;
  
  // Update Conteudo to maintain the invariant
  Conteudo := oldConteudo;
  
  // Prove postconditions
  assert a.Length == oldArray.Length * 2;
  assert a.Length >= defaultSize;
  assert cauda < a.Length;
  assert Conteudo == oldConteudo;
}
// </vc-helpers>

method enfileira(e:int)
    ensures Conteudo == old(Conteudo) + [e]
// </vc-spec>
// <vc-code>
{
  if cauda == a.Length {
    resize();
  }
  a[cauda] := e;
  cauda := cauda + 1;
  Conteudo := Conteudo + [e];
}
// </vc-code>

}
</full_file>