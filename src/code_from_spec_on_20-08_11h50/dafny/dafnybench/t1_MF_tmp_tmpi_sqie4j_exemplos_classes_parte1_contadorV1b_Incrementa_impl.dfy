class Contador
{
    var valor: int;

    //construtor anônimo
// <vc-spec>
    constructor ()
      ensures valor == 0
    {
        valor := 0;
    }

    //construtor com nome
    constructor Init(v:int)
      ensures valor == v
    {
        valor := v;
    }

// <vc-helpers>
// </vc-helpers>

method Incrementa()
      modifies this
      ensures valor == old(valor) + 1
// </vc-spec>
// <vc-code>
{
  valor := valor + 1;
}
// </vc-code>

}