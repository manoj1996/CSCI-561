class Node():
    """
    An object of this class is used to hold one predicate
    of a statement, used to construct a statement tree
    while parsing a statement and converting it to CNF.
    """

    def __init__(self, value, predicates_dict):
        self.value = value
        self.negation = False
        self.operator = True
        self.left = None
        self.right = None
        if value in predicates_dict:
            if '~' in predicates_dict[value]:
                self.negation = True
                predicates_dict[value] = predicates_dict[value][1:]
            self.operator = False

    def inorder_traversal(self, node):
        global traversal
        traversal = ''
        self.inorder(node)
        return traversal

    def inorder(self, node):
        global traversal
        if node:
            self.inorder(node.left)
            if node.negation:
                traversal += '~' + node.value
            else:
                traversal += node.value
            self.inorder(node.right)