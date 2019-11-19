from CNF import CNF
from Statement import *
import re
import copy
import collections
from Node import *
predicates_map = {}  # maintains predicates to constant mapping for a FOL stat
INPUT_FILE = 'input3.txt'
OUTPUT_FILE = 'output.txt'
KNOWLEDGE_BASE_HASH = {}
"""
Structure of KNOWLEDGE_BASE_HASH:
{
    "Predicate_Name" : set(stat_1, stat_2 ...) - that is set of stats objects
}
"""
KNOWLEDGE_BASE = set()
"""
Structure of KNOWLEDGE_BASE:
set([Statement Object 1, Statement Object 2 ...])
"""

def convert_postfix_to_tree(stat):
    """
    parses postfix representation of a stat and
    converts it to tree notation, where leaf nodes
    are predicate nodes and internal nodes are ops
    """
    stack = []
    r = re.compile('(~|&|\||=>|[A-Z][A-Z])')
    predicates = r.findall(stat)
    for token in predicates:
        if token in ['&', '|', '=>']:
            operand2 = stack.pop()
            operand1 = stack.pop()
            op = Node(token, predicates_map)
            op.left = operand1
            op.right = operand2
            stack.append(op)
        elif token == '~':
            stack[-1].negated = not stack[-1].negated
        else:
            operand = Node(token, predicates_map)
            stack.append(operand)
    return stack[0]


def convert_to_postfix(stat):
    """
    implementation of Shunting-Yard Algorithm
    to convert a infix stat to postfix stat
    """
    stack = []
    op_priority = {'~': 4, '&': 3, '|': 2, '=>': 1}  # ~: Not, &: And, |: Or, =>: Implication
    r = re.compile('(~|&|\||=>|[A-Z][A-Z]|\(|\))')
    predicates = r.findall(stat)
    postfix = ''
    for token in predicates:
        if re.match('[A-Z][A-Z]', token):
            postfix += token
        elif token in ['~', '&', '|', '=>']:
            while len(stack) != 0 and stack[-1] not in ['(', ')'] and op_priority[stack[-1]] >= op_priority[
                token]:
                postfix += stack.pop()
            stack.append(token)
        elif token == '(':
            stack.append(token)
        elif token == ')':
            while stack[-1] != '(':
                postfix += stack.pop()
            stack.pop()
    while stack:
        postfix += stack.pop()
    return postfix


def parse_input():
    """
    Parses the Query stats and the Knowledge base
    stats from the input file and returns them
    """
    QUERIES = []
    FOL_SENTENCES = []
    with open(INPUT_FILE) as f_input:
        file = list(f_input)
    f_input.close()
    NO_OF_QUERIES = int(file[0].rstrip('\n'))
    for query_line in file[1:1 + NO_OF_QUERIES]:
        query_line = query_line.rstrip()
        query_line = query_line.replace(' ', '')
        query_line = query_line.replace('\t', '')
        QUERIES.append(Predicate(query_line))
    NO_OF_FOL_SENTENCES = int(file[1 + NO_OF_QUERIES].rstrip('\n'))
    for fol_sentence in file[2 + NO_OF_QUERIES:2 + NO_OF_QUERIES + NO_OF_FOL_SENTENCES]:
        fol_sentence = fol_sentence.rstrip()
        fol_sentence = fol_sentence.replace(' ', '')
        fol_sentence = fol_sentence.replace('\t', '')
        FOL_SENTENCES.append(fol_sentence)
    FOL_SENTENCES = list(collections.OrderedDict.fromkeys(FOL_SENTENCES))
    return QUERIES, FOL_SENTENCES


def prepare_knowledgebase(FOL_SENTENCES):
    """
    Takes a set of FOL stats and performs
    preprocessing for converting them to CNF form
    adds the converted CNF stats to KNOWLEDGE_BASE and
    updates the KNOWLEDGE_BASE_HASH
    """
    global predicates_map
    cnf = CNF()
    for stat in FOL_SENTENCES:
        predicates_map.clear()
        stat, predicates_map = cnf.replace_predicate_by_constant(stat)
        stat = convert_to_postfix(stat)
        root = convert_postfix_to_tree(stat)  # convert to expression tree
        cnf.remove_implication(root)  # remove implication
        cnf.propagate_negated(root)  # propagate negated
        cnf.distribute_and_over_or(root, predicates_map)  # distribute AND over OR
        inorder = Node.inorder_traversal(root, root)
        stat = cnf.replace_constant_by_predicate(inorder, predicates_map)
        stats = stat.split('&')
        stats = cnf.standardize_variables(stats)
        for cnf_stmt in stats:
            stmt_obj = Statement(cnf_stmt)
            stmt_obj.add_stat_to_knowledge_base(KNOWLEDGE_BASE, KNOWLEDGE_BASE_HASH)


def display_knowledgebase(knowledge_base, knowledge_base_hash=None):
    """
    takes Knowledge base and KNOWLEDGE_BASE_HASH as arguments
    """
    print("\nKNOWLEDGE_BASE\n")
    for stat in knowledge_base:
        print(stat)
    print('Total No. of Statements : ', len(knowledge_base))
    if knowledge_base_hash:
        print("\nKNOWLEDGE_BASE_HASH\n")
        for key, val in knowledge_base_hash.items():
            print(key, ':', len(val), ' Statements')


def FOL_Resolution(knowledge_base, knowledge_base_hash, query):
    """
    Performs resolution of knowledge_base and query using Set of Set
    approach where knowledge_base is one set and knowledge_base2 is the second set
    query is the stat to be proved using resolution
    Returns: True if a contradiction is found and hence query
    is proved to be True
    else False if query cannot be proved from the Knowledge base
    """
    knowledge_base2 = set()
    knowledge_base_hash = {}
    query.add_stat_to_knowledge_base(knowledge_base2, knowledge_base_hash)
    query.add_stat_to_knowledge_base(knowledge_base, knowledge_base_hash)
    while True:
        history = {}  # maintains mapping of stats that have been resolved earlier
        new_stats = set()
        for stat1 in knowledge_base:
            # get possible set of stats with which the current stat cant be resolved
            resolving_clauses = stat1.get_resolving_clauses(knowledge_base_hash)
            for stat2 in resolving_clauses:
                if stat1 == stat2:
                    continue  # avoids resolution of a stat with itself
                flag1 = False
                flag2 = False
                if stat2.logic_stat_string in history:
                    flag1 = True
                    if stat1.logic_stat_string in history[stat2.logic_stat_string]:
                        history[stat2.logic_stat_string].discard(stat1.logic_stat_string)
                        continue  # avoids resolving two stats that appear in history
                if stat1.logic_stat_string in history:
                    flag2 = True
                    if stat2.logic_stat_string in history[stat1.logic_stat_string]:
                        history[stat1.logic_stat_string].discard(stat2.logic_stat_string)
                        continue  # avoids resolving two stats that appear in history
                # update history
                if flag2:
                    history[stat1.logic_stat_string].add(stat2.logic_stat_string)
                else:
                    history[stat1.logic_stat_string] = {stat2.logic_stat_string}
                resolvents = stat1.resolve(stat2)  # resolve stat1 with stat2
                if resolvents == False:  # contradiction found, return True
                    return True
                new_stats = new_stats.union(resolvents)
        if new_stats.issubset(knowledge_base):
            return False  # returns False if no new Knowledge is infered
        new_stats = new_stats.difference(knowledge_base)
        # update Knowledge base 2 to contains newly infered stats only
        knowledge_base2 = set()
        knowledge_base_hash = {}
        for stmt in new_stats:
            stmt.add_stat_to_knowledge_base(knowledge_base2, knowledge_base_hash)
        # add newly infered stats to Knowledge base 1 as well
        # to allow resoltion between newly infered stats
        knowledge_base = knowledge_base.union(new_stats)


def write_output(result):
    """
    writes output of a query to OUTPUT_FILE
    """

    with open(OUTPUT_FILE, 'w+') as f_output:
        f_output.write(output.strip())
    f_output.close()


def factor_stats(stat_set):
    """
    removes duplicate predicates from a set
    of stats and returns factored stats
    """
    for stat in stat_set:
        new_predicate_set = set()
        predicate_list = list(stat.predicate_set)
        for index, predicate1 in enumerate(predicate_list):
            for predicate2 in predicate_list[index + 1:]:
                if predicate1.negated == predicate2.negated:
                    substitution = predicate1.unify_with_predicate(predicate2)
                    if substitution == False:
                        continue
                    else:
                        for pred in predicate_list:
                            pred.substitute(substitution)
        stat.init_from_predicate_set(set(predicate_list))
    return stat_set

if __name__ == "__main__":
    QUERIES, FOL_SENTENCES = parse_input()
    prepare_knowledgebase(FOL_SENTENCES)
    output = ""
    # performs resolution for each query
    # negates the query, prepares a stat for the negated query,
    # prepares a new copy of Knowledge base and Hash
    # Performs resoltion and writes result
    for query_predicate in QUERIES:
        query_predicate.negate()
        query_predicate = Statement(query_predicate.predicate_string)
        knowledge_base = copy.deepcopy(KNOWLEDGE_BASE)
        knowledge_base_hash = copy.deepcopy(KNOWLEDGE_BASE_HASH)
        satisfiability = FOL_Resolution(knowledge_base, knowledge_base_hash, query_predicate)
        output += 'TRUE' + '\n' if satisfiability else 'FALSE' + '\n'
    display_knowledgebase(KNOWLEDGE_BASE, KNOWLEDGE_BASE_HASH)
    write_output(output)