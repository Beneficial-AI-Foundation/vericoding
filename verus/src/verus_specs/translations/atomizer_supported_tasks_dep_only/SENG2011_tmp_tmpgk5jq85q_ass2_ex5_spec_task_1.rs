pub fn Expon23(n: nat)
    requires n >= 0
    ensures ((expo(2, 3 * n) - expo(3, n))) % 5 == 0
{
    
}

pub fn check() {
    
}