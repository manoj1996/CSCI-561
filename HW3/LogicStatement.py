from Predicate import *
import copy

class LogicStatement():

    def __init__(self, logic_stat_string=None):
        if logic_stat_string:
            pred_list = logic_stat_string.split('|')
            pred_list = list(map(lambda x: Predicate(x), pred_list))
            self.pred_set = set(pred_list)
            self.logic_stat_string = '|'.join(list(map(lambda x: x.pred_string, self.pred_set)))
        else:
            self.logic_stat_string, self.pred_set = None, None

    def __hash__(self):
        return hash((''.join(sorted(self.logic_stat_string))))

    def init_from_pred_set(self, pred_set):
        self.pred_set = pred_set
        logic_stat_string_list = list(map(lambda x: x.pred_string, pred_set))
        self.logic_stat_string = '|'.join(logic_stat_string_list)

    def __eq__(self, stat):
        return self.pred_set == stat.pred_set

    def __str__(self):
        return self.logic_stat_string


    def add_stat_to_knowledge_base(self, knowledge_base, knowledge_base_hash):
        knowledge_base.add(self)
        for index, pred in enumerate(self.pred_set):
            if pred.name not in knowledge_base_hash:
                knowledge_base_hash[pred.name] = {self}
            else:
                knowledge_base_hash[pred.name].add(self)

    def resolve(self, stat):
        inferred_stats = set()
        for i, pred_1 in enumerate(self.pred_set):
            for j, pred_2 in enumerate(stat.pred_set):
                unification = False
                if (pred_1.negated ^ pred_2.negated):
                    if pred_1.name == pred_2.name:
                        unification = pred_1.unify_with_pred(pred_2)
                if unification == False:
                    continue
                else:
                    rest_stat_1, rest_stat_2 = copy.deepcopy(self.pred_set), copy.deepcopy(stat.pred_set)
                    rest_stat_1 = list(filter(lambda y: False if y == pred_1 else True, rest_stat_1))
                    rest_stat_2 = list(filter(lambda y: False if y == pred_2 else True, rest_stat_2))
                    if not rest_stat_1:
                        if not rest_stat_2:
                            return False
                    rest_stat_1 = list(map(lambda y: y.substitute(unification), rest_stat_1))
                    rest_stat_2 = list(map(lambda y: y.substitute(unification), rest_stat_2))
                    new_stat = LogicStatement()
                    new_stat.init_from_pred_set({*rest_stat_1, *rest_stat_2})
                    inferred_stats.add(new_stat)
        return inferred_stats

    def get_resolving_clauses(self, knowledge_base_hash):
        resolving_clauses = set()
        for pred in self.pred_set:
            if pred.name in knowledge_base_hash:
                resolving_clauses = {i for j in (resolving_clauses, knowledge_base_hash[pred.name]) for i in j}
        return resolving_clauses
