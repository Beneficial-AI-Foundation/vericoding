pub fn deserialiseAux<T>(codes: Seq<Code<T>>, trees: Seq<Tree<T>>) -> Seq<Tree<T>>
    requires(codes.len() > 0 || trees.len() > 0)
    ensures(|result: Seq<Tree<T>>| result.len() >= 0)
{
}

pub fn deserialise<T>(s: Seq<Code<T>>) -> Seq<Tree<T>>
    requires(s.len() > 0)
{
}

pub fn testDeserializeWithASingleNode()
{
}