class Predicate():
    def __init__(self, pred):
        self.operator = {'neg': '~', 'and': '&', 'or': '|', 'implies': '=>', 'openBr': '(', 'closedBr': ')'}
        split_pred = pred.split(self.operator['openBr'])
        self.negated = False
        self.name = split_pred[0]
        self.pred_string = pred
        parameters = split_pred[1][:-1]  # remove closing parenthesis
        self.arguments = parameters.split(',')
        if self.operator['neg'] in split_pred[0]:
            self.name = split_pred[0][1:]
            self.negated = True


    def __str__(self):
        return self.operator['neg'][not self.negated:] + self.name + self.operator['openBr'] + ','.join(self.arguments) + self.operator['closedBr']

    def __eq__(self, pred):
        return self.__dict__ == pred.__dict__

    def __hash__(self):
        return hash((self.pred_string))

    def negate(self):
        self.negated = not self.negated
        self.pred_string = self.operator['neg'][not self.negated:] + self.name + self.operator['openBr'] + ','.join(self.arguments) + self.operator['closedBr']

    def unify_with_pred(self, pred):
        substitute = {}
        if self.name == pred.name:
            if len(self.arguments) == len(pred.arguments):
                return unify(self.arguments, pred.arguments, substitute)
        return False

    def substitute(self, substitute):
        if substitute:
            index = 0
            for arg in self.arguments:
                if arg in substitute:
                    self.arguments[index] = substitute[arg]
                index += 1
            self.pred_string = self.operator['neg'][not self.negated:] + self.name + self.operator['openBr'] + ','.join(self.arguments) + self.operator['closedBr']
        return self

def unify(pred1_arg, pred2_arg, substitute):
    def unify_var(var, x, substitute):
        pred1, pred2, sub = None, None, None
        if var in substitute:
            pred1 = substitute[var]
            pred2 = x
            sub = True
        elif x in substitute:
            pred1 = var
            pred2 = substitute[x]
            sub = True
        else:
            sub = False
        if sub:
            return unify(pred1, pred2, substitute)
        else:
            substitute[var] = x
            return substitute
    if substitute == False:
        return False
    elif pred1_arg.__eq__(pred2_arg):
        return substitute
    elif type(pred1_arg) == str and pred1_arg.islower():
        return unify_var(pred1_arg, pred2_arg, substitute)
    elif type(pred2_arg) == str and pred2_arg.islower():
        return unify_var(pred2_arg, pred1_arg, substitute)
    elif type(pred1_arg) == list and type(pred2_arg) == list:
        if pred1_arg is not None:
            if pred2_arg is not None:
                return unify(pred1_arg[1:], pred2_arg[1:], unify(pred1_arg[0], pred2_arg[0], substitute))
        return substitute
    else:
        return False