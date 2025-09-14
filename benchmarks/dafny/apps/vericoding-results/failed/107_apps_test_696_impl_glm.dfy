predicate ValidInput(p: int) {
    2 <= p < 2000
}

function CountPrimitiveRoots(p: int): int
    requires ValidInput(p)
{
    if p == 2 then 1
    else |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1) % j == 0 && i % j == 0))|
}

// <vc-helpers>
predicate coprime(a: int, b: int)
    requires a > 0 && b > 0
{
    forall j :: 2 <= j <= a ==> !(b % j == 0 && a % j == 0)
}

function EulerPhi(n: nat): nat
    requires n >= 1
{
    if n == 1 then 1
    else |set i | 1 <= i < n && coprime(i, n)|
}

lemma lemma_coprime_iff(a: int, b: int)
    requires a > 0 && b > 0
    ensures coprime(a, b) <==> (forall j :: 2 <= j <= a ==> !(b % j == 0 && a % j == 0))
{
    reveal coprime();
}

lemma lemma_primitive_roots_count(p: int)
    requires ValidInput(p)
    ensures CountPrimitiveRoots(p) == EulerPhi(p-1)
{
    if p == 2 {
        assert CountPrimitiveRoots(2) == 1;
        assert EulerPhi(1) == 1;
    } else {
        reveal CountPrimitiveRoots();
        reveal EulerPhi();
        calc {
            CountPrimitiveRoots(p);
            |set i | 1 <= i < p-1 && (forall j :: 2 <= j <= i ==> !((p-1)%j==0 && i%j==0))|;
            {
                forall i {
                    lemma_coprime_iff(i, p-1);
                }
            }
            |set i | 1 <= i < p-1 && coprime(i, p-1)|;
            EulerPhi(p-1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(p: int) returns (result: int)
    requires ValidInput(p)
    ensures result >= 0
    ensures result == CountPrimitiveRoots(p)
// </vc-spec>
// <vc-code>
{
    lemma_primitive_roots_count(p);
    return EulerPhi(p-1);
}
// </vc-code>

