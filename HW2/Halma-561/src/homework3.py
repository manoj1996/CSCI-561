import math
import time


class Square:
    sBlank = 0  # blank square '.'
    sWhite = 1  # blank W square which is also W's goal square
    sBlack = 2  # blank B square which is also B's goal square

    pBlank = 0  # blank no pawn "."
    pWhite = 1  # White pawn
    pBlack = 2  # Black pawn

    # Constructor to initialize the square object -> halma positions
    def __init__(self, square=0, pawn=0, row=0, col=0):
        self.square = square
        self.pawn = pawn
        self.row = row
        self.col = col
        self.location = (row, col)


class Halma():
    # map -> {"pawn starting location" : {"final end point reachable from start" : [list of intermediate square locations] }
    moveMap = {}

    # Create initial board setup to define goals squares
    def __init__(self, boardSize=16, playerColor=Square.pBlack):

        board = [[None] * boardSize for _ in range(boardSize)]
        for row in range(boardSize):
            for col in range(boardSize):
                if row + col < 5:
                    element = Square(2, 2, row, col)
                elif 0 < row < 5 and row + col == 5:
                    element = Square(2, 2, row, col)
                elif row + col > 2 * (boardSize - 3) - 1:
                    element = Square(1, 1, row, col)
                elif boardSize - 1 > row > 10 and row + col == 2 * (boardSize - 3) - 1:
                    element = Square(1, 1, row, col)
                else:
                    element = Square(0, 0, row, col)

                board[row][col] = element

        # Save variables
        self.boardSize = boardSize
        self.board = board
        self.playerColor = playerColor
        self.alphaBetaEnabled = True
        self.bBaseLoc = {t.location: None for row in board for t in row if t.square == Square.pBlack}
        self.wBaseLoc = {t.location: None for row in board for t in row if t.square == Square.pWhite}
        self.bGoalLoc = self.wBaseLoc
        self.wGoalLoc = self.bBaseLoc
        self.bGoals = {t: None for row in board for t in row if t.square == Square.pWhite}
        self.wGoals = {t: None for row in board for t in row if t.square == Square.pBlack}
        self.agent = None
        self.ai = None
        if playerColor == Square.pBlack:
            self.agent = Square.pBlack
            self.ai = Square.pWhite
        else:
            self.agent = Square.pWhite
            self.ai = Square.pBlack
        self.evaluationCriteria = self.evaluate

    def updateBoard(self, board):
        self.board = board

    def changeEvaluationCriteria(self):
        self.evaluationCriteria = self.evaluationFunction

    def minimax(self, depth, maxPlayer, maxTime, originalPlayer, alpha=float("-inf"), beta=float("inf"), maxNode=True,
                prunes=0, boards=0):
        if maxPlayer == Square.pBlack:
            ai = Square.pWhite
        else:
            ai = Square.pBlack

        # Base case when either we hit the last node or we have a winner or if time limit exceeds
        if depth == 0 or self.determineWinner(maxPlayer) or time.time() > maxTime:
            return self.evaluationCriteria(maxPlayer, ai), None, prunes, boards

        # Initial val, alpha and beta variables are setup
        bestMove = None
        if maxNode:
            bestVal = float("-inf")
            moves = self.getNextMoves(maxPlayer, originalPlayer)
        else:
            bestVal = float("inf")
            moves = self.getNextMoves((Square.pBlack if maxPlayer == Square.pWhite else Square.pWhite), originalPlayer)

        # For each move
        for move in moves:
            for to in move["to"]:

                # Stop if time limit exceeds
                if time.time() > maxTime:
                    return bestVal, bestMove, prunes, boards

                # Move pawn and make the previous pawn location as blank
                fromPawn = move["from"].pawn
                move["from"].pawn = Square.pBlank
                to.pawn = fromPawn
                boards += 1
                # Recursively call self
                val, _, newPrunes, newBoards = self.minimax(depth - 1, maxPlayer, maxTime, originalPlayer, alpha, beta,
                                                            not maxNode, prunes, boards)
                prunes = newPrunes
                boards = newBoards

                # Move the pawn back to original position -> Refactor the board
                to.pawn = Square.pBlank
                move["from"].pawn = fromPawn

                if maxNode and val > bestVal:
                    bestVal = val
                    bestMove = (move["from"].location, to.location)
                    alpha = max(alpha, val)

                if not maxNode and val < bestVal:
                    bestVal = val
                    bestMove = (move["from"].location, to.location)
                    beta = min(beta, val)

                if self.alphaBetaEnabled and beta <= alpha:
                    return bestVal, bestMove, prunes + 1, boards

        return bestVal, bestMove, prunes, boards

    def getNextMoves(self, player=1, originalPlayer=1):
        # if player == originalPlayer:
        moves = []
        priorityTwoMove = []
        priorityOneMove = []
        tempMoves = []
        checkGoals = self.bGoalLoc
        checkBase = self.bBaseLoc
        if player == Square.pWhite:
            checkBase = self.wBaseLoc
            checkGoals = self.wGoalLoc
        for row in range(self.boardSize):
            for col in range(self.boardSize):
                currentSquare = self.board[row][col]

                # Skip squares that doesn't contain the player's pawns
                if currentSquare.pawn != player:
                    continue

                # List of moves from "from" to all possible final positions reachable from this
                if currentSquare.location not in self.moveMap:
                    self.moveMap[currentSquare.location] = {}
                move = {
                    "from": currentSquare,
                    "to": self.getMovesAtSquare(currentSquare, player, currentSquare, originalPlayer)
                }
                if len(move["to"]) == 0:
                    continue
                tempMove = move["to"][:]
                tempMove1 = move["to"][:]
                if player == originalPlayer:
                    if move["from"].location in checkBase:
                        moveFrom = move["from"].location
                        for t in tempMove:
                            if player == 2 and self.manhattanDistance(t.location, [0, 0]) <= self.manhattanDistance(moveFrom, [0, 0]):
                                tempMove1.remove(t)
                            elif player == 1 and self.manhattanDistance(moveFrom, [15, 15]) >= self.manhattanDistance(t.location, [15, 15]):
                                tempMove1.remove(t)
                        if len(tempMove1) == 0:
                            continue
                        tempMove2 = tempMove1[:]
                        for t in tempMove2:
                            if t.location in checkBase:
                                tempMove1.remove(t)
                        if len(tempMove1) == 0:
                            move["to"] = tempMove2
                            tempMoves.append(move)

                        else:
                            move["to"] = tempMove1
                            priorityOneMove.append(move)

                    elif move["from"].location in checkGoals:
                        tempMove = move["to"][:]
                        for t in tempMove:
                            if t.location not in checkGoals:
                                move["to"].remove(t)
                        if len(move["to"]):
                            priorityTwoMove.append(move)
                        else:
                            continue

                    else:
                        tempMove = move["to"][:]
                        for t in tempMove:
                            if t.location not in checkGoals:
                                move["to"].remove(t)
                        if len(move["to"]):
                            priorityTwoMove.append(move)
                        else:
                            move["to"] = tempMove
                            priorityTwoMove.append(move)
                else:
                    priorityOneMove.append(move)
        if player == originalPlayer:
            if len(priorityOneMove) == 0 and len(tempMoves):
                moves = tempMoves
            elif len(priorityOneMove) > 0:
                moves = priorityOneMove
            elif len(priorityTwoMove) > 0:
                moves = priorityTwoMove
        else:
            moves = priorityOneMove
        return moves

    def getMovesAtSquare(self, square, player, oldSquare, originalPlayer, moves=None, adjacent=True):

        if moves is None:
            moves = []

        row = square.location[0]
        col = square.location[1]

        # List of valid square types to move to
        validSquares = [Square.sBlank, Square.sWhite, Square.sBlack]

        # Removing moves that take the player out of the his enemy's initial position
        if square.square != Square.sBlank and square.square != player:
            validSquares.remove(Square.sBlank)
            validSquares.remove(player)

        notTrack = False
        # Find and save immediately adjacent moves
        if oldSquare.location not in self.moveMap and player == originalPlayer:
            self.moveMap[oldSquare.location] = {}

        if square.location not in self.moveMap[oldSquare.location] and player == originalPlayer:
            self.moveMap[oldSquare.location][square.location] = set()
        else:
            notTrack = True

        for colDelta in range(-1, 2):
            for rowDelta in range(-1, 2):

                # Check adjacent Squares
                newRow = row + rowDelta
                newCol = col + colDelta

                # Skip checking degenerate values
                if (
                        newRow == row and newCol == col) or newRow < 0 or newCol < 0 or newRow >= self.boardSize or newCol >= self.boardSize:
                    continue

                # Handle moves that don't take to valid end points
                preJumpSquare = self.board[newRow][newCol]

                if preJumpSquare.square not in validSquares:
                    continue
                if preJumpSquare.pawn == Square.pBlank and preJumpSquare.location is not square.location:
                    if adjacent:  # Don't consider adjacent on subsequent calls
                        moves.append(preJumpSquare)
                        if player == originalPlayer and not notTrack:
                            self.moveMap[oldSquare.location][square.location].add(preJumpSquare.location)
                    continue

                # Check jump squares
                newRow = newRow + rowDelta
                newCol = newCol + colDelta

                # Skip checking degenerate values
                if (
                        newRow == row and newCol == col) or newRow < 0 or newCol < 0 or newRow >= self.boardSize or newCol >= self.boardSize:
                    continue

                # Handle moves that don't take to valid end points

                jumpSquare = self.board[newRow][newCol]

                if jumpSquare in moves or (jumpSquare.square not in validSquares):
                    continue
                if jumpSquare.pawn == Square.pBlank and jumpSquare.location is not square.location:
                    # Prioritize jumps over single adjacent moves
                    moves.insert(0, jumpSquare)
                    if player == originalPlayer and not notTrack:
                        self.moveMap[oldSquare.location][square.location].add(jumpSquare.location)
                    self.getMovesAtSquare(jumpSquare, player, oldSquare, originalPlayer, moves, False)
        return moves

    def manhattanDistance(self, p0, p1):
        dx = abs(p0[0] - p1[0])
        dy = abs(p0[1] - p1[1])
        return dx + dy

    def eucleideanDistance(self, source, destination):
        x_source, y_source = source
        x_destination, y_destination = destination
        return 100 * math.sqrt((x_destination - x_source) ** 2 + (y_destination - y_source) ** 2)

    def chebyshevDistance(self, p0, p1):
        dx = abs(p0[0] - p1[0])
        dy = abs(p0[1] - p1[1])
        # Chebyshev constants
        D = 1
        D2 = 1
        return D * (dx + dy) + (D2 - 2 * D) * min(dx, dy)

    def numPiecesTarget(self, player):
        if player == Square.pBlack:
            l = [1 for g in self.bGoalLoc if self.board[g[0]][g[1]].pawn == Square.pBlack]
        else:
            l = [1 for g in self.wGoalLoc if self.board[g[0]][g[1]].pawn == Square.pWhite]
        return len(l)

    def numPiecesBase(self, player):
        if player == Square.pBlack:
            l = [1 for g in self.bBaseLoc if self.board[g[0]][g[1]].pawn == Square.pBlack]
        else:
            l = [1 for g in self.wBaseLoc if self.board[g[0]][g[1]].pawn == Square.pWhite]
        return len(l)

    def determineWinner(self, p):
        if p == Square.pWhite:
            if all(self.board[g[0]][g[1]].pawn == Square.pWhite for g in self.wGoalLoc):
                return Square.pWhite
        elif p == Square.pBlack:
            if all(self.board[g[0]][g[1]].pawn == Square.pBlack for g in self.bGoalLoc):
                return Square.pBlack
        return None

    def sumOfAllDistances(self, p):
        distance = 0
        for row in range(self.boardSize):
            for col in range(self.boardSize):
                distanceHeuristic = self.chebyshevDistance
                square = self.board[row][col]
                if square.pawn == p and p == Square.pWhite:
                    if self.numPiecesTarget(p) < 12:
                        distance += distanceHeuristic(square.location, (0, 0))
                    else:
                        distanceHeuristic = self.manhattanDistance
                        distances = [distanceHeuristic(square.location, g) for g in
                                     self.wGoalLoc if self.board[g[0]][g[1]].pawn != Square.pWhite]
                        distance += max(distances) if len(distances) else 1000
                elif square.pawn == p and p == Square.pBlack:
                    if self.numPiecesTarget(p) < 12:
                        distance += distanceHeuristic(square.location, (15, 15))
                    else:
                        distanceHeuristic = self.manhattanDistance
                        distances = [distanceHeuristic(square.location, g) for g in
                                     self.bGoalLoc if self.board[g[0]][g[1]].pawn != Square.pBlack]
                        distance += max(distances) if len(distances) else 1000

        return distance

    def evaluate(self, p, opp):
        checkAgentWin = self.determineWinner(self.agent)
        checkAiWin = self.determineWinner(self.ai)
        agentScore = self.sumOfAllDistances(p)
        aiScore = self.sumOfAllDistances(opp)
        agentTargets = 10 * self.numPiecesTarget(self.agent)
        aiTargets = 10 * self.numPiecesTarget(self.ai)

        if checkAgentWin:
            return 20000
        elif checkAiWin:
            return -20000

        if p == self.ai:
            return -aiScore + agentScore + aiTargets
        else:
            return -agentScore + aiScore + agentTargets

    def evaluationFunction(self, p, opp):

        value = 0
        distanceHeuristic = self.manhattanDistance
        for col in range(self.boardSize):
            for row in range(self.boardSize):

                square = self.board[row][col]

                if square.pawn == Square.pWhite:
                    distances = [distanceHeuristic(square.location, g) for g in self.wGoalLoc if
                                 self.board[g[0]][g[1]].pawn != Square.pWhite]
                    value -= max(distances) if len(distances) else -50

                elif square.pawn == Square.pBlack:
                    distances = [distanceHeuristic(square.location, g) for g in self.bGoalLoc if
                                 self.board[g[0]][g[1]].pawn != Square.pBlack]
                    value += max(distances) if len(distances) else -50

        if self.playerColor == Square.pBlack:
            value *= -1

        return value

    def getMovePath(self, moves, start, stop):
        stack = [(start, [start])]
        visited = set()
        while stack:
            (vertex, path) = stack.pop()
            if vertex not in visited:
                if vertex == stop:
                    return path
                visited.add(vertex)
                for neighbor in moves[vertex]:
                    if neighbor in moves:
                        stack.append((neighbor, path + [neighbor]))
                    elif neighbor == stop:
                        stack.append((neighbor, path + [neighbor]))


if __name__ == "__main__":
    start = time.time()
    fileInput = list()
    with open("input.txt", "r") as f:
        for record in f.readlines():
            fileInput.append(record.strip())
        f.close()
    game = fileInput[0]
    playerColor = fileInput[1]
    timeRemaining = float(fileInput[2])
    boardConfig = list()
    for i in range(3, len(fileInput)):
        boardConfig.append([char for char in fileInput[i]])

    currentBoardConfig = list()
    for row in range(len(boardConfig)):
        currentBoardRow = list()
        for col in range(len(boardConfig[0])):
            if boardConfig[row][col] == 'B':
                pawn = Square(2, 2, row, col)
            elif boardConfig[row][col] == 'W':
                pawn = Square(1, 1, row, col)
            elif boardConfig[row][col] == '.':
                pawn = Square(0, 0, row, col)
            currentBoardRow.append(pawn)
        currentBoardConfig.append(currentBoardRow)

    if playerColor.lower() == "white":
        playerTurn = Square.pWhite
    else:
        playerTurn = Square.pBlack

    h = Halma(16, playerTurn)
    h.updateBoard(currentBoardConfig)
    if h.numPiecesTarget(playerTurn) > 8 or h.numPiecesBase(playerTurn) > 0:
        treeDepthSearch = 3
    else:
        treeDepthSearch = 2

    if h.numPiecesTarget(playerTurn) > 10:
        h.changeEvaluationCriteria()
    # print("Tree depth - ", str(treeDepthSearch))
    maxAvailableTime = time.time() + timeRemaining
    maxAvailableTimeTurn = min(time.time() + 20, maxAvailableTime)
    _, move, prunes, boards = h.minimax(treeDepthSearch, playerTurn, maxAvailableTimeTurn, playerTurn)
    # prevMove, finalMove = None, None
    if move:
        # print("Total number of boards/nodes generated : ", boards)
        # print("Moves:", move)
        # print("Total number of nodes pruned :", prunes)
        output = ""
        if (abs(move[0][0] - move[1][0]) == 1 or abs(move[0][1] - move[1][1])) == 1:
            output = "E " + str(move[0][1]) + "," + str(move[0][0]) + " " + str(move[1][1]) + "," + str(move[1][0])
            # prevMove = (move[0][1], move[0][0])
            # finalMove = (move[1][1], move[1][0])
        else:
            output = ""
            pathList = h.getMovePath(h.moveMap[move[0]], move[0], move[1])
            i = 0
            j = 1
            # prevMove = (pathList[0][1], pathList[0][0])
            while j != len(pathList):
                output += "J " + str(pathList[i][1]) + "," + str(pathList[i][0]) + " " + str(
                    pathList[j][1]) + "," + str(
                    pathList[j][0]) + "\n"
                i += 1
                j += 1
            # finalMove = (pathList[len(pathList) - 1][1], pathList[len(pathList) - 1][0])
        with open("output.txt", "w+") as fWrite:
            fWrite.write(output.strip())
        end = time.time()
    else:
        print("Invalid game configuration or player already won")
        end = time.time()
    # boardConfig[prevMove[1]][prevMove[0]] = "."
    # if playerColor.lower() == "white":
    #     boardConfig[finalMove[1]][finalMove[0]] = "W"
    #     oppColor = "BLACK"
    # else:
    #     boardConfig[finalMove[1]][finalMove[0]] = "B"
    #     oppColor = "WHITE"
    #
    # sOutput = ""
    #
    # sOutput += str(game) + "\n" + str(oppColor) + "\n" + str(timeRemaining) + "\n"
    # for r in range(len(boardConfig)):
    #     s = ""
    #     for c in range(len(boardConfig[0])):
    #         s += str(boardConfig[r][c])
    #     s += "\n"
    #     sOutput += s
    # with open("input.txt", "w+") as f1:
    #     f1.write(sOutput)
    # Print search result stats
    # print("Time to compute : ", round(end - start, 4))
