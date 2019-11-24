import copy
import re
from DOM import *
class CNF():

    def __init__(self):
        self.upper_case_letters = list(map(chr, range(65, 75)))
        self.lower_case_letters = list(map(chr, range(97, 107)))
        self.standard_variable_count = 0
        self.operator = {'neg':'~', 'and':'&', 'or':'|', 'implies':'=>', 'openBr':'(', 'closedBr':')'}

    def remove_implication(self, dom):
        if dom:
            self.remove_implication(dom.left)
            if dom.op is not None and dom.val == self.operator['implies']:
                dom.val = self.operator['or']
                dom.left.negated = not dom.left.negated
            self.remove_implication(dom.right)

    def assign_pred_constant(self, count, uppercase):
        start = count + 10
        str_constant = ''
        while start >= 10:
            val = start % 10
            if uppercase:
                str_constant = self.upper_case_letters[val] + str_constant
            else:
                str_constant = self.lower_case_letters[val] + str_constant
            start //= 10
        if uppercase:
            str_constant = self.upper_case_letters[start - 1] + str_constant
        else:
            str_constant = self.lower_case_letters[start - 1] + str_constant
        return str_constant

    def replace_pred_by_constant(self, statement):
        r = re.compile('~?[A-Z][A-Za-z0-9]*\([a-zA-Z0-9][a-zA-Z,0-9]*\)')
        preds = r.findall(statement)
        preds_map = {}
        pred_list = list(set(preds))
        for index in range(len(pred_list)):
            pred_constant = self.assign_pred_constant(index, True)
            preds_map[pred_constant] = pred_list[index]
            statement = statement.replace(pred_list[index], pred_constant)
        return statement, preds_map


    def standardize_variables(self, statements):
        standard_statements = []
        for statement in statements:
            variable_dict = {}
            r = re.compile('\([a-zA-Z,]+\)')
            parameters = list(set(list(filter(lambda x: x.islower(), (','.join(list(map(lambda x: x[1:-1], r.findall(statement))))).split(',')))))
            for para in parameters:
                variable_dict[para] = self.assign_pred_constant(self.standard_variable_count, False)
                self.standard_variable_count += 1
            preds = statement.split(self.operator['or'])
            pred_list = []
            for pred in preds:
                parts = pred.split(self.operator['openBr'])
                parameters = parts[1][:-1].split(',')
                parameters = list(map(lambda x: variable_dict[x] if x in variable_dict else x, parameters))
                pred = parts[0] + self.operator['openBr'] + ','.join(parameters) + self.operator['closedBr']
                pred_list.append(pred)
            standard_statements.append(self.operator['or'].join(pred_list))
        return standard_statements

    def replace_constant_by_pred(self, statement, preds_map):
        for key, val in preds_map.items():
            statement = statement.replace(key, val)
        return statement

    def move_negation_inside(self, dom):
        if dom:
            if dom.op:
                if dom.negated:
                    dom.negated = False
                    dom.left.negated, dom.right.negated = not dom.left.negated, not dom.right.negated
                    if dom.val == self.operator['and']:
                        dom.val = self.operator['or']
                    else:
                        dom.val = self.operator['and']

            self.move_negation_inside(dom.right)
            self.move_negation_inside(dom.left)

    def distribute_and_over_or(self, dom, preds_map):
        if dom:
            if dom.val == self.operator['or']:
                if dom.left.val == self.operator['and'] and dom.right.val == self.operator['and']:
                    left_and, right_and = dom.left, dom.right

                    a, b, c, d = left_and.left, left_and.right, right_and.left, right_and.right
                    a_copy, b_copy, c_copy, d_copy = copy.deepcopy(a), copy.deepcopy(b), copy.deepcopy(c), copy.deepcopy(d)

                    left_or_1 = DOM(self.operator['or'], preds_map)
                    left_or_2 = DOM(self.operator['or'], preds_map)
                    right_or_1 = DOM(self.operator['or'], preds_map)
                    right_or_2 = DOM(self.operator['or'], preds_map)
                    dom.val = self.operator['and']
                    left_and.left, left_and.right, right_and.left, right_and.right = left_or_1, left_or_2, right_or_1, right_or_2

                    left_or_1.left, left_or_1.right = a, c
                    left_or_2.left, left_or_2.right = a_copy, d
                    right_or_1.left, right_or_1.right = b, c_copy
                    right_or_2.left, right_or_2.right = b_copy, d_copy
                elif dom.left.op and not dom.right.op and dom.left.val == self.operator['and']:
                    c, a = dom.left.right, a = dom.right
                    a_copy = copy.deepcopy(a)
                    right_or = DOM(self.operator['or'], preds_map)
                    dom.val = self.operator['and']
                    dom.left.val = self.operator['or']
                    dom.left.right = a
                    dom.right = right_or
                    right_or.left, right_or.right = c, a_copy
                elif not dom.left.op and dom.right.op and dom.right.val == self.operator['and']:
                    a = dom.left
                    a_copy = copy.deepcopy(a)
                    b = dom.right.left
                    left_or = DOM(self.operator['or'], preds_map)
                    dom.val = self.operator['and']
                    dom.right.val = self.operator['or']
                    dom.left = left_or
                    left_or.left, left_or.right = a, b
                    dom.right.left = a_copy
            self.distribute_and_over_or(dom.left, preds_map)
            self.distribute_and_over_or(dom.right, preds_map)