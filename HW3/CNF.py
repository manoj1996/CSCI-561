import copy
import re
from Node import *
class CNF():

    def __init__(self):
        self.upper_case_letters = list(map(chr, range(65, 91)))
        self.lower_case_letters = list(map(chr, range(97, 123)))
        self.standard_variable_count = 0

    def remove_implication(self, node):
        """
        A=>B is equivalent to ~A|B
        thus this method performs implication removal
        """
        if node:
            self.remove_implication(node.left)
            if node.op and node.val == '=>':
                node.val = '|'
                node.left.negated = not node.left.negated
            self.remove_implication(node.right)

    def assign_predicate_constant(self, count, uppercase):
        """
        count >= 0
        uppercase : if True then constant begin from AA, else from aa
        returns a string constant for count val
        """
        start = count + 26
        str_constant = ''
        while start >= 26:
            val = start % 26
            if uppercase:
                str_constant = self.upper_case_letters[val] + str_constant
            else:
                str_constant = self.lower_case_letters[val] + str_constant
            start //= 26
        if uppercase:
            str_constant = self.upper_case_letters[start - 1] + str_constant
        else:
            str_constant = self.lower_case_letters[start - 1] + str_constant
        return str_constant

    def replace_predicate_by_constant(self, statement):
        """
        replaces a predicate string by a string
        constant of length 2, for easy parsing
        ex: Mother(x,y) can be replaced by AB
        """
        r = re.compile('~?[A-Z][A-Za-z]*\([a-zA-Z][a-zA-Z,]*\)')
        predicates = r.findall(statement)
        predicates_map = {}
        predicate_list = list(set(predicates))
        for index in range(len(predicate_list)):
            predicate_constant = self.assign_predicate_constant(index, True)
            predicates_map[predicate_constant] = predicate_list[index]
            statement = statement.replace(predicate_list[index], predicate_constant)
        return statement, predicates_map


    def standardize_variables(self, statements):
        """
        takes list of CNF statements strings as argument
        return them as list of standardized CNF statements,
        standardizes the variables for all the statements
        """

        standard_statements = []
        for statement in statements:
            variable_dict = {}
            r = re.compile('\([a-zA-Z,]+\)')
            parameters = r.findall(statement)
            parameters = list(map(lambda x: x[1:-1], parameters))
            parameters = ','.join(parameters)
            parameters = parameters.split(',')
            parameters = list(filter(lambda x: x.islower(), parameters))
            parameters = list(set(parameters))
            for para in parameters:
                variable_dict[para] = self.assign_predicate_constant(self.standard_variable_count, False)
                self.standard_variable_count += 1
            predicates = statement.split('|')
            predicate_list = []
            for predicate in predicates:
                parts = predicate.split('(')
                parameters = parts[1][:-1].split(',')
                parameters = list(map(lambda x: variable_dict[x] if x in variable_dict else x, parameters))
                predicate = parts[0] + '(' + ','.join(parameters) + ')'
                predicate_list.append(predicate)
            standard_statements.append('|'.join(predicate_list))
        return standard_statements

    def replace_constant_by_predicate(self, statement, predicates_map):
        """
        restores predicate string in place of constants
        for getting the original statement back
        """
        for key, val in predicates_map.items():
            statement = statement.replace(key, val)
        return statement

    def propagate_negated(self, node):
        """
        moves negated inside and hence applies De Morgans law
        """
        if node:
            if node.op and node.negated:
                node.left.negated = not node.left.negated
                node.right.negated = not node.right.negated
                if node.val == '&':
                    node.val = '|'
                else:
                    node.val = '&'
                node.negated = False
            self.propagate_negated(node.left)
            self.propagate_negated(node.right)

    def distribute_and_over_or(self, node, predicates_map):
        """
        distributes and over or in the step
        of converting an FOL statement to CNF
        """
        if node:
            if node.val == '|':
                if node.left.val == '&' and node.right.val == '&':  # OR as parent, two AND as its children
                    left_and = node.left
                    right_and = node.right
                    a = left_and.left
                    b = left_and.right
                    c = right_and.left
                    d = right_and.right
                    a_copy = copy.deepcopy(a)
                    b_copy = copy.deepcopy(b)
                    c_copy = copy.deepcopy(c)
                    d_copy = copy.deepcopy(d)
                    left_or_1 = Node('|', predicates_map)
                    left_or_2 = Node('|', predicates_map)
                    right_or_1 = Node('|', predicates_map)
                    right_or_2 = Node('|', predicates_map)
                    node.val = '&'
                    left_and.left = left_or_1
                    left_and.right = left_or_2
                    right_and.left = right_or_1
                    right_and.right = right_or_2
                    left_or_1.left = a
                    left_or_1.right = c
                    left_or_2.left = a_copy
                    left_or_2.right = d
                    right_or_1.left = b
                    right_or_1.right = c_copy
                    right_or_2.left = b_copy
                    right_or_2.right = d_copy
                elif node.left.op and not node.right.op and node.left.val == '&':
                    c = node.left.right
                    a = node.right
                    a_copy = copy.deepcopy(a)
                    right_or = Node('|', predicates_map)
                    node.val = '&'
                    node.left.val = '|'
                    node.left.right = a
                    node.right = right_or
                    right_or.left = c
                    right_or.right = a_copy
                elif not node.left.op and node.right.op and node.right.val == '&':
                    a = node.left
                    a_copy = copy.deepcopy(a)
                    b = node.right.left
                    left_or = Node('|', predicates_map)
                    node.val = '&'
                    node.right.val = '|'
                    node.left = left_or
                    left_or.left = a
                    left_or.right = b
                    node.right.left = a_copy
            self.distribute_and_over_or(node.left, predicates_map)
            self.distribute_and_over_or(node.right, predicates_map)