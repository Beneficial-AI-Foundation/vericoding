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

method GetValor() returns (v:int)
      ensures v == valor
// </vc-spec>
// <vc-code>
{
  v := valor;
}
// </vc-code>

}