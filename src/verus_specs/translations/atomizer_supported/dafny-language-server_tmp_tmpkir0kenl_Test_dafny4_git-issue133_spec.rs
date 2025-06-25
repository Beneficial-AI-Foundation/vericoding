datatype State = State { m: Map<int, bool> }

proof fn Test(s: State)
    requires 42 in s.m
    ensures s.spec_update_m(s.m.insert(42, s.m[42])) == s
{
}

datatype MyDt = MakeA(int, bool) | MakeB { s: Multiset<int>, t: State }

proof fn AnotherTest(a: MyDt, b: MyDt, c: bool)
    requires a.is_MakeB() && b.is_MakeB()
    requires a.get_MakeB_s() == a.get_MakeB_t().m.dom().to_multiset() && b.get_MakeB_s().len() == 0
    requires a.get_MakeB_t().m == Map::empty() && b.get_MakeB_t().m.len() == 0
{
}

datatype GenDt<X,Y> = Left(X) | Middle(X, int, Y) | Right { y: Y }

pub fn ChangeGen(g: GenDt)
{
}

datatype Recursive<X> = Red | Green { next: Recursive<X>, m: Set<X> }

proof fn RecLem(r: Recursive) -> (s: Recursive)
    ensures r == s
{
}