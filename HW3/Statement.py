from Predicate import *
import copy

class Statement():
    """
    Defines one FOL statement and the operations allowed on them
    member variables include:
    predicate_set : set of 'Predicate' objects which are
    connected via OR operator in a stat
    logic_stat_string : string representation of stat
    """

    def __init__(self, logic_stat_string=None):
        if logic_stat_string:
            predicate_list = logic_stat_string.split('|')
            predicate_list = list(map(lambda x: Predicate(x), predicate_list))
            self.predicate_set = set(predicate_list)
            logic_stat_string_list = list(map(lambda x: x.predicate_string, self.predicate_set))
            self.logic_stat_string = '|'.join(logic_stat_string_list)
        else:
            self.logic_stat_string = None
            self.predicate_set = None

    # def init_from_string(self, logic_stat_string):
    #     """
    #     initializes a Statement object from stat string
    #     """
    #     predicate_list = logic_stat_string.split('|')
    #     predicate_list = list(map(lambda x: Predicate(x), predicate_list))
    #     self.predicate_set = set(predicate_list)
    #     logic_stat_string_list = list(map(lambda x: x.predicate_string, self.predicate_set))
    #     self.logic_stat_string = '|'.join(logic_stat_string_list)

    def init_from_predicate_set(self, predicate_set):
        """
        initializes Statement object from a predicate set
        """
        self.predicate_set = predicate_set
        logic_stat_string_list = list(map(lambda x: x.predicate_string, predicate_set))
        self.logic_stat_string = '|'.join(logic_stat_string_list)

    def __str__(self):
        return self.logic_stat_string

    def __eq__(self, stat):
        return self.predicate_set == stat.predicate_set

    def __hash__(self):
        return hash((''.join(sorted(self.logic_stat_string))))

    def check_in_knowledge_base(self, knowledge_base):
        '''
        returns true if cnf statement already exists
        in the knowledge base else False
        '''
        if self in knowledge_base:
            return True
        return False

    def add_stat_to_knowledge_base(self, knowledge_base, knowledge_base_hash):
        """
        adds a stat in a knowledge base and updates the Hash
        """
        knowledge_base.add(self)
        for predicate in self.predicate_set:
            if predicate.name in knowledge_base_hash:
                knowledge_base_hash[predicate.name].add(self)
            else:
                knowledge_base_hash[predicate.name] = {self}

    def resolve(self, stat):
        '''
        Resolves two stats
        returns False if a contradiction is encountered when resolved otherwise,
        returns set of new inferred stats(empty if no stats inferred)
        '''
        inferred_stats = set()
        for predicate_1 in self.predicate_set:
            for predicate_2 in stat.predicate_set:
                unification = False
                if (predicate_1.negated ^ predicate_2.negated) and predicate_1.name == predicate_2.name:
                    unification = predicate_1.unify_with_predicate(
                        predicate_2)  # returns substitution if stats can unify else false
                if unification == False:
                    continue
                else:
                    rest_stat_1 = copy.deepcopy(self.predicate_set)
                    rest_stat_2 = copy.deepcopy(stat.predicate_set)
                    rest_stat_1 = list(filter(lambda x: False if x == predicate_1 else True, rest_stat_1))
                    rest_stat_2 = list(filter(lambda x: False if x == predicate_2 else True, rest_stat_2))
                    if not rest_stat_1 and not rest_stat_2:  # contradiction found
                        return False
                    rest_stat_1 = list(map(lambda x: x.substitute(unification), rest_stat_1))
                    rest_stat_2 = list(map(lambda x: x.substitute(unification), rest_stat_2))
                    new_stat = Statement()
                    new_stat.init_from_predicate_set(set(rest_stat_1 + rest_stat_2))
                    inferred_stats.add(new_stat)
        return inferred_stats

    def get_resolving_clauses(self, knowledge_base_hash):
        """
        returns a set of possible stats
        the self stat object can resolve with
        """
        resolving_clauses = set()
        for predicate in self.predicate_set:
            if predicate.name in knowledge_base_hash:
                resolving_clauses = resolving_clauses.union(knowledge_base_hash[predicate.name])
        return resolving_clauses
