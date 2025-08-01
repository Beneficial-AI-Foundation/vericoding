// Potência

// deve ser especificado a potência, porque ele não existe n dafny

// Função recursiva da potência
function Potencia(x:nat, y:nat):nat
{
    if y == 0
    then 1
    else x * Potencia(x,y-1)
}


// Quero agora implementar como uma função não recursiva
//IMPL 

// Quero agora implementar como uma função não recursiva
method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{
    var b := x;
    var e := y;
    r := 1;
    
    while e > 0
        invariant Potencia(b,e) * r == Potencia(x,y)
        decreases e
    {
        r := r * b;
        e := e - 1;
    }
}


// Devemos sempre construir uma tabela para vermos passo a passo o processo
// POT(2,3)
// x | y | b | e | r | 
// 2 | 3 | 2 | 3 | 1 |
// 2 | 3 | 2 | 2 | 1x2     |
// 2 | 3 | 2 | 1 | 1x2x2   |
// 2 | 3 | 2 | 0 | 1x2x2x2 |
// temos que na invariante queremos a fórmula x^y
// INV ... = x^y
// vendo pelo que foi processado fica dando o seguinte
// x | y | b | e | r |  
// 2 | 3 | 2 | 3 | 1 (2^0)      | 2^3 x 2^0 = 2^3
// 2 | 3 | 2 | 2 | 1x2  (2^1)   | 2^2 x 2^1 = 2^3
// 2 | 3 | 2 | 1 | 1x2x2 (2^2)  | 2^1 x 2^2 = 2^3
// 2 | 3 | 2 | 0 | 1x2x2x2 (2^3)| 2^0 x 2^3 = 2^3
// portanto a base está sendo feito a potencia de e (usando o potencia) e multiplicado pelo valor de r
// b^e * r
// assim temos a fórmula: b^e * r = x^y
// dai utilizamos a function potencia para construir a fórmula
// Potencia(b,e)*r == Potencia(x,y)