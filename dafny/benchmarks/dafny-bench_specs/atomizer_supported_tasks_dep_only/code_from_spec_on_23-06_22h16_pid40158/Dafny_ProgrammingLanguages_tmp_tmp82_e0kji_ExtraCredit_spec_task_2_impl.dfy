//ATOM Exp
datatype Exp = Const(n: int) | Add(left: Exp, right: Exp)

//ATOM eval
function eval(e: Exp): int
{
    match e
    case Const(n) => n
    case Add(left, right) => eval(left) + eval(right)
}

//ATOM optimize
function optimize(e: Exp): Exp
{
    match e
    case Const(n) => Const(n)
    case Add(left, right) => 
        var optLeft := optimize(left);
        var optRight := optimize(right);
        match (optLeft, optRight)
        case (Const(0), _) => optRight
        case (_, Const(0)) => optLeft
        case (Const(a), Const(b)) => Const(a + b)
        case _ => Add(optLeft, optRight)
}

//ATOM optimizeCorrect
lemma optimizeCorrect(e: Exp)
    ensures eval(optimize(e)) == eval(e)
{
    match e
    case Const(n) => {}
    case Add(left, right) => 
        optimizeCorrect(left);
        optimizeCorrect(right);
        var optLeft := optimize(left);
        var optRight := optimize(right);
        assert eval(optLeft) == eval(left);
        assert eval(optRight) == eval(right);
}

//IMPL optimizeFeatures
method optimizeFeatures()
{
}