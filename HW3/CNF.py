import copy
import re
from Node import *
class CNF():

    def __init__(self):
        self.upper_alpha_mapping = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z']
        self.lower_alpha_mapping = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']
        self.standard_variable_count = 0

    def remove_implication(self, node):
        """
        A=>B is equivalent to ~A|B
        thus this method performs implication removal
        """
        if node:
            self.remove_implication(node.left)
            if node.operator and node.value == '=>':
                node.value = '|'
                node.left.negation = not node.left.negation
            self.remove_implication(node.right)

    def give_constant(self, count, uppercase):
        """
        count >= 0
        uppercase : if True then constant begin from AA, else from aa
        returns a string constant for count value
        """
        start = count + 26
        str_constant = ''
        while start >= 26:
            val = start % 26
            if uppercase:
                str_constant = self.upper_alpha_mapping[val] + str_constant
            else:
                str_constant = self.lower_alpha_mapping[val] + str_constant
            start //= 26
        if uppercase:
            str_constant = self.upper_alpha_mapping[start - 1] + str_constant
        else:
            str_constant = self.lower_alpha_mapping[start - 1] + str_constant
        return str_constant

    def replace_predicate_by_constant(self, statement):
        """
        replaces a predicate string by a string
        constant of length 2, for easy parsing
        ex: Mother(x,y) can be replaced by AB
        """
        r = re.compile('~?[A-Z][A-Za-z]*\([a-zA-Z][a-zA-Z,]*\)')
        predicates = r.findall(statement)
        predicates_dict = {}
        for index, predicate in enumerate(set(predicates)):
            predicate_constant = self.give_constant(index, True)
            predicates_dict[predicate_constant] = predicate
            statement = statement.replace(predicate, predicate_constant)
        return statement, predicates_dict


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
                variable_dict[para] = self.give_constant(self.standard_variable_count, False)
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

    def replace_constant_by_predicate(self, statement, predicates_dict):
        """
        restores predicate string in place of constants
        for getting the original statement back
        """
        for key, value in predicates_dict.items():
            statement = statement.replace(key, value)
        return statement

    def propagate_negation(self, node):
        """
        moves negation inside and hence applies De Morgans law
        """
        if node:
            if node.operator and node.negation:
                node.left.negation = not node.left.negation
                node.right.negation = not node.right.negation
                if node.value == '&':
                    node.value = '|'
                else:
                    node.value = '&'
                node.negation = False
            self.propagate_negation(node.left)
            self.propagate_negation(node.right)

    def distribute_and_over_or(self, node, predicates_dict):
        """
        distributes and over or in the step
        of converting an FOL statement to CNF
        """
        if node:
            if node.value == '|':
                if node.left.value == '&' and node.right.value == '&':  # OR as parent, two AND as its children
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
                    left_or_1 = Node('|', predicates_dict)
                    left_or_2 = Node('|', predicates_dict)
                    right_or_1 = Node('|', predicates_dict)
                    right_or_2 = Node('|', predicates_dict)
                    node.value = '&'
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
                elif node.left.operator and not node.right.operator and node.left.value == '&':
                    c = node.left.right
                    a = node.right
                    a_copy = copy.deepcopy(a)
                    right_or = Node('|', predicates_dict)
                    node.value = '&'
                    node.left.value = '|'
                    node.left.right = a
                    node.right = right_or
                    right_or.left = c
                    right_or.right = a_copy
                elif not node.left.operator and node.right.operator and node.right.value == '&':
                    a = node.left
                    a_copy = copy.deepcopy(a)
                    b = node.right.left
                    left_or = Node('|', predicates_dict)
                    node.value = '&'
                    node.right.value = '|'
                    node.left = left_or
                    left_or.left = a
                    left_or.right = b
                    node.right.left = a_copy
            self.distribute_and_over_or(node.left, predicates_dict)
            self.distribute_and_over_or(node.right, predicates_dict)