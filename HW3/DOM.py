class DOM():

    def __init__(self, val, predicates_map):
        self.left, self.right = None, None
        self.val = val
        self.negate = '~'
        if val in predicates_map:
            self.op = False
            if self.negate in predicates_map[val]:
                predicates_map[val] = predicates_map[val][1:]
                self.negated = True
            else:
                self.negated = False
        else:
            self.op = True
            self.negated = False

    def inorder_traversal(self, dom):
        def inorder(dom):
            global traversal
            if dom:
                inorder(dom.left)
                if dom.negated:
                    traversal += self.negate + dom.val
                else:
                    traversal += dom.val
                inorder(dom.right)
        global traversal
        traversal = ''
        inorder(dom)
        return traversal