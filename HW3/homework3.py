from CNF import CNF
from Statement import *
import re
import copy
import collections
from Node import *
predicates_dict = {}  # maintains predicates to constant mapping for a FOL statement
INPUT_FILE = 'input2.txt'
OUTPUT_FILE = 'output.txt'
KNOWLEDGE_BASE_HASH = {}
"""
Structure of KNOWLEDGE_BASE_HASH:
{
    "Predicate_Name" : set(statement_1, statement_2 ...) - that is set of statements objects
}
"""
KNOWLEDGE_BASE = set()
"""
Structure of KNOWLEDGE_BASE:
set([Statement Object 1, Statement Object 2 ...])
"""

def convert_postfix_to_tree(statement):
    """
    parses postfix representation of a statement and
    converts it to tree notation, where leaf nodes
    are predicate nodes and internal nodes are operators
    """
    stack = []
    r = re.compile('(~|&|\||=>|[A-Z][A-Z])')
    predicates = r.findall(statement)
    for token in predicates:
        if token in ['&', '|', '=>']:
            operand2 = stack.pop()
            operand1 = stack.pop()
            operator = Node(token, predicates_dict)
            operator.left = operand1
            operator.right = operand2
            stack.append(operator)
        elif token == '~':
            stack[-1].negation = not stack[-1].negation
        else:
            operand = Node(token, predicates_dict)
            stack.append(operand)
    return stack[0]


def convert_to_postfix(statement):
    """
    implementation of Shunting-Yard Algorithm
    to convert a infix statement to postfix statement
    """
    stack = []
    operator_priority = {'~': 4, '&': 3, '|': 2, '=>': 1}  # ~: Not, &: And, |: Or, =>: Implication
    r = re.compile('(~|&|\||=>|[A-Z][A-Z]|\(|\))')
    predicates = r.findall(statement)
    postfix = ''
    for token in predicates:
        if re.match('[A-Z][A-Z]', token):
            postfix += token
        elif token in ['~', '&', '|', '=>']:
            while len(stack) != 0 and stack[-1] not in ['(', ')'] and operator_priority[stack[-1]] >= operator_priority[
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
    Parses the Query statements and the Knowledge base
    statements from the input file and returns them
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
    Takes a set of FOL statements and performs
    preprocessing for converting them to CNF form
    adds the converted CNF statements to KNOWLEDGE_BASE and
    updates the KNOWLEDGE_BASE_HASH
    """
    global predicates_dict
    cnf = CNF()
    for statement in FOL_SENTENCES:
        predicates_dict.clear()
        statement, predicates_dict = cnf.replace_predicate_by_constant(statement)
        statement = convert_to_postfix(statement)
        root = convert_postfix_to_tree(statement)  # convert to expression tree
        cnf.remove_implication(root)  # remove implication
        cnf.propagate_negation(root)  # propagate negation
        cnf.distribute_and_over_or(root, predicates_dict)  # distribute AND over OR
        inorder = Node.inorder_traversal(root, root)
        statement = cnf.replace_constant_by_predicate(inorder, predicates_dict)
        statements = statement.split('&')
        statements = cnf.standardize_variables(statements)
        for cnf_stmt in statements:
            stmt_obj = Statement(cnf_stmt)
            stmt_obj.add_statement_to_KB(KNOWLEDGE_BASE, KNOWLEDGE_BASE_HASH)


def display_knowledgebase(KB, KB_HASH=None):
    """
    takes Knowledge base and KNOWLEDGE_BASE_HASH as arguments
    """
    print("\nKNOWLEDGE_BASE\n")
    for statement in KB:
        print(statement)
    print('Total No. of Statements : ', len(KB))
    if KB_HASH:
        print("\nKNOWLEDGE_BASE_HASH\n")
        for key, value in KB_HASH.items():
            print(key, ':', len(value), ' Statements')


def FOL_Resolution(KB, KB_HASH, query):
    """
    Performs resolution of KB and query using Set of Set
    approach where KB is one set and KB2 is the second set
    query is the statement to be proved using resolution
    Returns: True if a contradiction is found and hence query
    is proved to be True
    else False if query cannot be proved from the Knowledge base
    """
    KB2 = set()
    KB_HASH = {}
    query.add_statement_to_KB(KB2, KB_HASH)
    query.add_statement_to_KB(KB, KB_HASH)
    while True:
        history = {}  # maintains mapping of statements that have been resolved earlier
        new_statements = set()
        for statement1 in KB:
            # get possible set of statements with which the current statement cant be resolved
            resolving_clauses = statement1.get_resolving_clauses(KB_HASH)
            for statement2 in resolving_clauses:
                if statement1 == statement2:
                    continue  # avoids resolution of a statement with itself
                flag1 = False
                flag2 = False
                if statement2.statement_string in history:
                    flag1 = True
                    if statement1.statement_string in history[statement2.statement_string]:
                        history[statement2.statement_string].discard(statement1.statement_string)
                        continue  # avoids resolving two statements that appear in history
                if statement1.statement_string in history:
                    flag2 = True
                    if statement2.statement_string in history[statement1.statement_string]:
                        history[statement1.statement_string].discard(statement2.statement_string)
                        continue  # avoids resolving two statements that appear in history
                # update history
                if flag2:
                    history[statement1.statement_string].add(statement2.statement_string)
                else:
                    history[statement1.statement_string] = {statement2.statement_string}
                resolvents = statement1.resolve(statement2)  # resolve statement1 with statement2
                if resolvents == False:  # contradiction found, return True
                    return True
                new_statements = new_statements.union(resolvents)
        if new_statements.issubset(KB):
            return False  # returns False if no new Knowledge is infered
        new_statements = new_statements.difference(KB)
        # update Knowledge base 2 to contains newly infered statements only
        KB2 = set()
        KB_HASH = {}
        for stmt in new_statements:
            stmt.add_statement_to_KB(KB2, KB_HASH)
        # add newly infered statements to Knowledge base 1 as well
        # to allow resoltion between newly infered statements
        KB = KB.union(new_statements)


def write_output(result):
    """
    writes output of a query to OUTPUT_FILE
    """

    with open(OUTPUT_FILE, 'w+') as f_output:
        f_output.write(output.strip())
    f_output.close()


def factor_statements(statement_set):
    """
    removes duplicate predicates from a set
    of statements and returns factored statements
    """
    for statement in statement_set:
        new_predicate_set = set()
        predicate_list = list(statement.predicate_set)
        for index, predicate1 in enumerate(predicate_list):
            for predicate2 in predicate_list[index + 1:]:
                if predicate1.negative == predicate2.negative:
                    substitution = predicate1.unify_with_predicate(predicate2)
                    if substitution == False:
                        continue
                    else:
                        for pred in predicate_list:
                            pred.substitute(substitution)
        statement.init_from_predicate_set(set(predicate_list))
    return statement_set

if __name__ == "__main__":
    QUERIES, FOL_SENTENCES = parse_input()
    prepare_knowledgebase(FOL_SENTENCES)
    output = ""
    # performs resolution for each query
    # negates the query, prepares a statement for the negated query,
    # prepares a new copy of Knowledge base and Hash
    # Performs resoltion and writes result
    for query_predicate in QUERIES:
        query_predicate.negate()
        query_predicate = Statement(query_predicate.predicate_string)
        KB = copy.deepcopy(KNOWLEDGE_BASE)
        KB_HASH = copy.deepcopy(KNOWLEDGE_BASE_HASH)
        satisfiability = FOL_Resolution(KB, KB_HASH, query_predicate)
        output += 'TRUE' + '\n' if satisfiability else 'FALSE' + '\n'
    display_knowledgebase(KNOWLEDGE_BASE, KNOWLEDGE_BASE_HASH)
    write_output(output)