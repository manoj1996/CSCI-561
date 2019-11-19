class Node():
    """
    An object of this class is used to hold one predicate
    of a statement, used to construct a statement tree
    while parsing a statement and converting it to CNF.
    """

    def __init__(self, val, predicates_map):
        self.val = val
        self.negated = False
        self.op = True
        self.left = None
        self.right = None
        if val in predicates_map:
            if '~' in predicates_map[val]:
                self.negated = True
                predicates_map[val] = predicates_map[val][1:]
            self.op = False

    def inorder_traversal(self, node):
        global traversal
        traversal = ''
        self.inorder(node)
        return traversal

    def inorder(self, node):
        global traversal
        if node:
            self.inorder(node.left)
            if node.negated:
                traversal += '~' + node.val
            else:
                traversal += node.val
            self.inorder(node.right)