// <vc-preamble>
class Contador
{
    var valor: int;

    //construtor anônimo
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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Decrementa()
      modifies this
      ensures valor == old(valor) - 1
// </vc-spec>
// <vc-code>
{
        valor := valor -1 ;
}
// </vc-code>

}