predicate ValidInput(n: int) {
    n >= 2 && n % 2 == 0 && n <= 20
}

function ExpectedResult(n: int): int
    requires ValidInput(n)
{
    var half := n / 2;
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    (binomial * arrangements) / 2
}

// <vc-helpers>
function factorial(n: int): int
    requires 0 <= n <= 20
    ensures factorial(n) > 0
{
    if n == 0 then 1 else n * factorial(n-1)
}

lemma CentralBinomialCoefficientProperties(n: int)
    requires ValidInput(n)
    ensures factorial(n) % (factorial(n/2) * factorial(n/2)) == 0
    ensures (factorial(n) / (factorial(n/2) * factorial(n/2))) % 2 == 0
{
    if n == 2 {
        calc {
            factorial(2);
            2;
            { assert factorial(1)==1; }
            2;
            ==> 
            2 % (1*1) == 0;
        }
        calc {
            factorial(2) / (factorial(1)*factorial(1));
            2 / 1;
            2;
            ==>
            2 % 2 == 0;
        }
    } else if n == 4 {
        calc {
            factorial(4);
            24;
            { assert factorial(2)==2; }
            24;
            ==>
            24 % (2*2) == 0;
        }
        calc {
            factorial(4) / (factorial(2)*factorial(2));
            24 / 4;
            6;
            ==>
            6 % 2 == 0;
        }
    } else if n == 6 {
        calc {
            factorial(6);
            720;
            { assert factorial(3)==6; }
            720;
            ==>
            720 % (6*6) == 0;
        }
        calc {
            factorial(6) / (factorial(3)*factorial(3));
            720 / 36;
            20;
            ==>
            20 % 2 == 0;
        }
    } else if n == 8 {
        calc {
            factorial(8);
            40320;
            { assert factorial(4)==24; }
            40320;
            ==>
            40320 % (24*24) == 0;
        }
        calc {
            factorial(8) / (factorial(4)*factorial(4));
            40320 / 576;
            70;
            ==>
            70 % 2 == 0;
        }
    } else if n == 10 {
        calc {
            factorial(10);
            3628800;
            { assert factorial(5)==120; }
            3628800;
            ==>
            3628800 % (120*120) == 0;
        }
        calc {
            factorial(10) / (factorial(5)*factorial(5));
            3628800 / 14400;
            252;
            ==>
            252 % 2 == 0;
        }
    } else if n == 12 {
        calc {
            factorial(12);
            479001600;
            { assert factorial(6)==720; }
            479001600;
            ==>
            479001600 % (720*720) == 0;
        }
        calc {
            factorial(12) / (factorial(6)*factorial(6));
            479001600 / 518400;
            924;
            ==>
            924 % 2 == 0;
        }
    } else if n == 14 {
        calc {
            factorial(14);
            87178291200;
            { assert factorial(7)==5040; }
            87178291200;
            ==>
            87178291200 % (5040*5040) == 0;
        }
        calc {
            factorial(14) / (factorial(7)*factorial(7));
            87178291200 / 25401600;
            3432;
            ==>
            3432 % 2 == 0;
        }
    } else if n == 16 {
        calc {
            factorial(16);
            20922789888000;
            { assert factorial(8)==40320; }
            20922789888000;
            ==>
            20922789888000 % (40320*40320) == 0;
        }
        calc {
            factorial(16) / (factorial(8)*factorial(8));
            20922789888000 / 1625702400;
            12870;
            ==>
            12870 % 2 == 0;
        }
    } else if n == 18 {
        calc {
            factorial(18);
            6402373705728000;
            { assert factorial(9)==362880; }
            6402373705728000;
            ==>
            6402373705728000 % (362880*362880) == 0;
        }
        calc {
            factorial(18) / (factorial(9)*factorial(9));
            6402373705728000 / 131681894400;
            48620;
            ==>
            48620 % 2 == 0;
        }
    } else {
        assert n == 20;
        calc {
            factorial(20);
            2432902008176640000;
            { assert factorial(10)==3628800; }
            2432902008176640000;
            ==>
            2432902008176640000 % (3628800*3628800) == 0;
        }
        calc {
            factorial(20) / (factorial(10)*factorial(10));
            2432902008176640000 / 13168189440000;
            184756;
            ==>
            184756 % 2 == 0;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == ExpectedResult(n)
    ensures result > 0
// </vc-spec>
// <vc-code>
{
    var half := n / 2;
    var factN := factorial(n);
    var factHalf := factorial(half);
    var factHalfMinus1 := factorial(half - 1);
    CentralBinomialCoefficientProperties(n);
    var binomial := factN / (factHalf * factHalf);
    var arrangements := factHalfMinus1 * factHalfMinus1;
    result := (binomial * arrangements) / 2;
}
// </vc-code>

