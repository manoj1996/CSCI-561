from CNF import CNF
from LogicStatement import *
import re
import collections
import time
from DOM import *
preds_map = {}  # maintains preds to constant mapping for a FOL stat
INPUT_FILE = 'input13.txt'
OUTPUT_FILE = 'output.txt'
KNOWLEDGE_BASE_HASH = {}
KNOWLEDGE_BASE = set()
operator = {'neg':'~', 'and':'&', 'or':'|', 'implies':'=>', 'openBr':'(', 'closedBr':')'}
def convert_postfix_to_tree(stat):
    stack = []
    r = re.compile('(~|&|\||=>|[A-Z][A-Z])')
    preds = r.findall(stat)
    for token in preds:
        if token in [operator['and'], operator['or'], operator['implies']]:
            operand2 = stack.pop()
            operand1 = stack.pop()
            op = DOM(token, preds_map)
            op.left = operand1
            op.right = operand2
            stack.append(op)
        elif token == operator['neg']:
            stack[-1].negated = not stack[-1].negated
        else:
            operand = DOM(token, preds_map)
            stack.append(operand)
    return stack[0]


def convert_to_postfix(stat):
    stack = []
    r = re.compile('(~|&|\||=>|[A-Z][A-Z]|\(|\))')
    preds = r.findall(stat)
    expression = ''
    op_priority = {operator['neg']: 4, operator['and']: 3, operator['or']: 2, operator['implies']: 1}
    for i, token in enumerate(preds):
        if re.match('[A-Z][A-Z]', token):
            expression += token
        elif token in [operator['neg'], operator['and'], operator['or'], operator['implies']]:
            while len(stack) != 0 and stack[-1] not in [operator['openBr'], operator['closedBr']] and op_priority[stack[-1]] >= op_priority[
                token]:
                t = stack[-1]
                expression += t
                del stack[-1]
            stack.append(token)
        elif token == operator['openBr']:
            stack.append(token)
        elif token == operator['closedBr']:
            while stack[-1] != operator['openBr']:
                t = stack[-1]
                expression += t
                del stack[-1]
            del stack[-1]
    while stack:
        t = stack[-1]
        expression += t
        stack = stack[:-1]
    return expression


def parse_input():
    fol_sentences = []
    queries = []
    file_input = list()
    with open(INPUT_FILE, "r") as f:
        for record in f.readlines():
            file_input.append(record.strip())
    f.close()
    no_queries = int(file_input[0])
    for query_line in range(1, 1 + no_queries):
        query = file_input[query_line].replace(' ', '')
        query = query.replace('\t', '')
        queries.append(Predicate(query))
    no_fol_sentences = int(file_input[1 + no_queries])
    for sentence_num in range(2 + no_queries, 2 + no_queries + no_fol_sentences):
        fol_sentence = file_input[sentence_num].replace(' ', '')
        fol_sentence = fol_sentence.replace('\t', '')
        fol_sentences.append(fol_sentence)
    fol_sentences = list(collections.OrderedDict.fromkeys(fol_sentences))
    return queries, fol_sentences


def prepare_knowledgebase(FOL_SENTENCES):
    global preds_map
    cnf = CNF()
    for stat in FOL_SENTENCES:
        preds_map.clear()
        stat, preds_map = cnf.replace_pred_by_constant(stat)
        stat = convert_to_postfix(stat)
        root = convert_postfix_to_tree(stat)  # convert to expression tree
        cnf.remove_implication(root)  # remove implication
        cnf.move_negation_inside(root)  # propagate negated
        cnf.distribute_and_over_or(root, preds_map)  # distribute AND over OR
        inorder = DOM.inorder_traversal(root, root)
        stat = cnf.replace_constant_by_pred(inorder, preds_map)
        stats = stat.split(operator['and'])
        stats = cnf.standardize_variables(stats)
        for cnf_stmt in stats:
            stmt_obj = LogicStatement(cnf_stmt)
            stmt_obj.add_stat_to_knowledge_base(KNOWLEDGE_BASE, KNOWLEDGE_BASE_HASH)


def display_knowledgebase(knowledge_base, knowledge_base_hash=None):
    print("\nKNOWLEDGE BASE\n")
    if knowledge_base is not None:
        for index, val in enumerate(knowledge_base):
            print(val)
    print('Total No. of Logic Statements : ', len(knowledge_base))
    if knowledge_base_hash is not None:
        print("\nKNOWLEDGE BASE HASH\n")
        for key in knowledge_base_hash:
            print(key, ':', len(knowledge_base_hash[key]), ' Logic Statements')


def FOL_Resolution(knowledge_base_copy, query, query_start_time):
    knowledge_base2 = set()
    knowledge_base_hash_copy = {}
    query.add_stat_to_knowledge_base(knowledge_base2, knowledge_base_hash_copy)
    query.add_stat_to_knowledge_base(knowledge_base_copy, knowledge_base_hash_copy)
    while True:
        history = {}
        new_stats = set()
        for i, stat1 in enumerate(knowledge_base_copy):
            resolving_clauses = stat1.get_resolving_clauses(knowledge_base_hash_copy)
            for j, stat2 in enumerate(resolving_clauses):
                if time.time() - query_start_time > 1:
                    return False
                if stat1 == stat2:
                    continue
                flag2 = False
                if stat2.logic_stat_string in history and stat1.logic_stat_string in history[stat2.logic_stat_string]:
                    history[stat2.logic_stat_string].remove(stat1.logic_stat_string)
                    continue
                if stat1.logic_stat_string in history:
                    flag2 = True
                    if stat2.logic_stat_string in history[stat1.logic_stat_string]:
                        history[stat1.logic_stat_string].remove(stat2.logic_stat_string)
                        continue
                if flag2 == False:
                    history[stat1.logic_stat_string] = {stat2.logic_stat_string}
                else:
                    history[stat1.logic_stat_string].add(stat2.logic_stat_string)
                resolvents = stat1.resolve(stat2)
                if resolvents == False:
                    return True
                # else:
                #     count += 1
                # if count > 20000:
                #     return False
                new_stats = new_stats.union(resolvents)
        knowledge_base_hash_copy = {}
        knowledge_base2 = set()
        if new_stats.issubset(knowledge_base_copy):
            return False
        new_stats = new_stats.difference(knowledge_base_copy)
        for i, stmt in enumerate(new_stats):
            stmt.add_stat_to_knowledge_base(knowledge_base2, knowledge_base_hash_copy)
        knowledge_base_copy = knowledge_base_copy.union(new_stats)


def factor_stats(stat_set):
    for stat in stat_set:
        pred_list = list(stat.pred_set)
        index = -1
        for pred1 in pred_list:
            index += 1
            for pred2 in pred_list[index + 1:]:
                if pred1.negated == pred2.negated:
                    substitution = pred1.unify_with_pred(pred2)
                    if substitution:
                        for pred in pred_list:
                            pred.substitute(substitution)
                    else:
                        continue
        stat.init_from_pred_set(set(pred_list))
    return stat_set

if __name__ == "__main__":
    queries, fol_sentences = parse_input()
    prepare_knowledgebase(fol_sentences)
    output = ""
    start = time.time()
    for query_pred in queries:
        query_pred.negate()
        query_pred = LogicStatement(query_pred.pred_string)
        knowledge_base = set(KNOWLEDGE_BASE)
        knowledge_base_hash = dict(KNOWLEDGE_BASE_HASH)
        query_start_time = time.time()
        satisfiability = FOL_Resolution(knowledge_base, query_pred, query_start_time)
        output += 'TRUE' + '\n' if satisfiability else 'FALSE' + '\n'
    # display_knowledgebase(KNOWLEDGE_BASE, KNOWLEDGE_BASE_HASH)
    with open(OUTPUT_FILE, 'w+') as f_output:
        f_output.write(output.strip())
    f_output.close()
    print("Execution time:{0:.2f}".format(time.time()-start)+'s')