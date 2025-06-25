pub fn insertRecursion(tree: Tree, value: int) -> (res: Tree)
    requires(BinarySearchTree(tree))
    ensures(res != Empty ==> BinarySearchTree(res))
    ensures(forall |x| minValue(tree, x) && x < value ==> minValue(res, x))
    ensures(forall |x| maxValue(tree, x) && x > value ==> maxValue(res, x))
{
}