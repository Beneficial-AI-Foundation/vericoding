// <vc-preamble>
/*
    OK fila de tamanho ilimitado com arrays circulares
    OK representação ghost: coleção de elementos da fila e qualquer outra informação necessária
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
  var a: array<int>;
  var cauda: nat;
  const defaultSize: nat;

  ghost var Conteudo: seq<int>;

  // invariante
  ghost predicate Valid()  {
                        defaultSize > 0
    && a.Length >= defaultSize
    && 0 <= cauda <= a.Length
    && Conteudo == a[0..cauda]
    }

    // inicia fila com 3 elementos
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

  method enfileira(e:int)
    ensures Conteudo == old(Conteudo) + [e]
    {

    if (cauda == a.Length) {
      var novoArray := new int[cauda + defaultSize];
      var i := 0;

      forall i | 0 <= i < a.Length
    {
        novoArray[i] := a[i];
    }
      a := novoArray;
    }

    a[cauda] := e;
    cauda := cauda + 1;
    Conteudo := Conteudo + [e];
    }
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method concat(f2: Fila) returns (r: Fila)
    requires Valid()
    requires f2.Valid()
    ensures r.Conteudo == Conteudo + f2.Conteudo
// </vc-spec>
// <vc-code>
{
    r := new Fila();

    var i:= 0;

    while i < cauda
      invariant 0 <= i <= cauda
      invariant 0 <= i <= r.cauda
      invariant r.cauda <= r.a.Length
      invariant fresh(r.Repr)
      invariant r.Valid()
      invariant r.Conteudo == Conteudo[0..i]
    {
      var valor := a[i];
      r.enfileira(valor);
      i := i + 1;
    }

    var j := 0;
    while j < f2.cauda
      invariant 0 <= j <= f2.cauda
      invariant 0 <= j <= r.cauda
      invariant r.cauda <= r.a.Length
      invariant fresh(r.Repr)
      invariant r.Valid()
      invariant r.Conteudo == Conteudo + f2.Conteudo[0..j]
    {
      var valor := f2.a[j];
      r.enfileira(valor);
      j := j + 1;
    }
}
// </vc-code>

}