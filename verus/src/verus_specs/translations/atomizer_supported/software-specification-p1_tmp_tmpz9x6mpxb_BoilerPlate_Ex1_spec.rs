// ATOM 
pub enum Tree<V> {
    Leaf(V),
    SingleNode(V, Box<Tree<V>>),
    DoubleNode(V, Box<Tree<V>>, Box<Tree<V>>)
}
// ATOM 

pub enum Code<V> {
    CLf(V),
    CSNd(V),
    CDNd(V)
}

// ATOM 
pub spec fn serialise<V>(t: Tree<V>) -> Seq<Code<V>>
{
    match t {
        Tree::Leaf(v) => seq![Code::CLf(v)],
        Tree::SingleNode(v, t) => serialise(*t) + seq![Code::CSNd(v)],
        Tree::DoubleNode(v, t1, t2) => serialise(*t2) + serialise(*t1) + seq![Code::CDNd(v)]
    }
}

// Ex 1
// ATOM 

// Ex 1
pub spec fn deserialiseAux<T>(codes: Seq<Code<T>>, trees: Seq<Tree<T>>) -> Seq<Tree<T>>
    requires
        codes.len() > 0 || trees.len() > 0
    ensures
        |result| >= 0
{
    if codes.len() == 0 {
        trees
    } else {
        match codes[0] {
            Code::CLf(v) => deserialiseAux(codes.subrange(1, codes.len() as int), trees + seq![Tree::Leaf(v)]),
            Code::CSNd(v) => if trees.len() >= 1 {
                deserialiseAux(codes.subrange(1, codes.len() as int), trees.subrange(0, trees.len() - 1) + seq![Tree::SingleNode(v, Box::new(trees[trees.len() - 1]))])
            } else {
                trees
            },
            Code::CDNd(v) => if trees.len() >= 2 {
                deserialiseAux(codes.subrange(1, codes.len() as int), trees.subrange(0, trees.len() - 2) + seq![Tree::DoubleNode(v, Box::new(trees[trees.len() - 1]), Box::new(trees[trees.len() - 2]))])
            } else {
                trees
            }
        }
    }
}

// ATOM 
pub spec fn deserialise<T>(s: Seq<Code<T>>) -> Seq<Tree<T>>
    requires
        s.len() > 0
{
    deserialiseAux(s, seq![])
}

// Ex 2
// SPEC 

// Ex 2
pub fn testSerializeWithASingleLeaf() {
}

// SPEC 
pub fn testSerializeNullValues() {
}

// SPEC 
pub fn testSerializeWithAllElements() {
}

// Ex 3 

// SPEC 

// Ex 3 
pub fn testDeseraliseWithASingleLeaf() {
}

// SPEC 
pub fn testDeserializeWithASingleNode() {
}

// SPEC 
pub fn testDeserialiseWithAllElements() {
}

// Ex 4 
// ATOM 

// Ex 4 
pub proof fn SerialiseLemma<V>(t: Tree<V>)
    ensures
        deserialise(serialise(t)) == seq![t]
{
}

// ATOM 
pub proof fn DeserialisetAfterSerialiseLemma<T>(t: Tree<T>, cds: Seq<Code<T>>, ts: Seq<Tree<T>>) 
    ensures
        deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + seq![t])
{
}