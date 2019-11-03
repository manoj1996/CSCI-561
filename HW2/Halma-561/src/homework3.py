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
    def __init__(self, boardSize=16):

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
        self.alphaBetaEnabled = True
        self.bBaseLoc = {t.location: None for row in board for t in row if t.square == Square.pBlack}
        self.wBaseLoc = {t.location: None for row in board for t in row if t.square == Square.pWhite}
        self.bGoalLoc = self.wBaseLoc
        self.wGoalLoc = self.bBaseLoc
        self.bGoals = {t: None for row in board for t in row if t.square == Square.pWhite}
        self.wGoals = {t: None for row in board for t in row if t.square == Square.pBlack}

    def updateBoard(self, board):
        self.board = board

    def minimax(self, depth, maxPlayer, maxTime, originalPlayer, alpha=float("-inf"), beta=float("inf"), maxNode=True,
                prunes=0, boards=0):

        # Base case when either we hit the last node or we have a winner or if time limit exceeds
        if depth == 0 or self.determineWinner() or time.time() > maxTime:
            return self.evaluationFunction(maxPlayer), None, prunes, boards

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

                if self.alphaBetaEnabled and not maxNode and alpha >= val:
                    return bestVal, bestMove, prunes + 1, boards
                if self.alphaBetaEnabled and maxNode and val >= beta:
                    return bestVal, bestMove, prunes + 1, boards

        return bestVal, bestMove, prunes, boards

    def getNextMoves(self, player=1, originalPlayer=1):
        if player == originalPlayer:
            priorityTwoMove = []
            priorityThreeMove = []
        priorityOneMove = []
        tempMoves = []
        checkGoals = self.bGoalLoc
        checkBase = self.bBaseLoc
        if player == Square.pWhite:
            checkBase = self.wBaseLoc
            checkGoals = self.wGoalLoc
        for col in range(self.boardSize):
            for row in range(self.boardSize):
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
                if player == originalPlayer:
                    if move["from"].location in checkBase:
                        for t in move["to"]:
                            if t.location in checkBase:
                                move["to"].remove(t)
                        if len(move["to"]) == 0:
                            move["to"] = tempMove
                            tempMoves.append(move)
                        else:
                            priorityOneMove.append(move)

                    elif move["from"].location not in checkGoals:
                        priorityTwoMove.append(move)
                    else:
                        priorityThreeMove.append(move)
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
                moves = priorityThreeMove
        else:
            moves = priorityOneMove
        return moves

    def getMovesAtSquare(self, square, player, oldSquare, originalPlayer, moves=None, adjacent=True):

        if moves is None:
            moves = []

        row = square.location[0]
        col = square.location[1]

        checkBase = self.bBaseLoc
        if player == Square.pWhite:
            checkBase = self.wBaseLoc
        basePawn = False
        if square.location in checkBase:
            basePawn = True
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

                        if player == 2 and basePawn:
                            if (preJumpSquare.location[0] > square.location[0]) and (
                                    preJumpSquare.location[1] > square.location[1]):
                                moves.append(preJumpSquare)
                                if player == originalPlayer and not notTrack:
                                    self.moveMap[oldSquare.location][square.location].add(preJumpSquare.location)

                            continue
                        if player == 1 and basePawn:
                            if (preJumpSquare.location[0] < square.location[0]) and (
                                    preJumpSquare.location[1] < square.location[1]):
                                moves.append(preJumpSquare)
                                if player == originalPlayer and not notTrack:
                                    self.moveMap[oldSquare.location][square.location].add(preJumpSquare.location)
                            continue
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
                    if player == 2 and basePawn:
                        if (jumpSquare.location[0] > square.location[0]) and (
                                jumpSquare.location[1] > square.location[1]):
                            moves.insert(0, jumpSquare)
                            if player == originalPlayer and not notTrack:
                                self.moveMap[oldSquare.location][square.location].add(jumpSquare.location)
                            self.getMovesAtSquare(jumpSquare, player, oldSquare, originalPlayer, moves, False)
                        continue
                    if player == 1 and basePawn:
                        if (jumpSquare.location[0] < square.location[0]) and (
                                jumpSquare.location[1] < square.location[1]):
                            moves.insert(0, jumpSquare)
                            if player == originalPlayer and not notTrack:
                                self.moveMap[oldSquare.location][square.location].add(jumpSquare.location)
                            self.getMovesAtSquare(jumpSquare, player, oldSquare, originalPlayer, moves, False)
                        continue

                    moves.insert(0, jumpSquare)
                    if player == originalPlayer and not notTrack:
                        self.moveMap[oldSquare.location][square.location].add(jumpSquare.location)
                    self.getMovesAtSquare(jumpSquare, player, oldSquare, originalPlayer, moves, False)
        return moves

    def determineWinner(self):

        if all(self.board[g.location[0]][g.location[1]].pawn == Square.pWhite for g in self.wGoals):
            return Square.pWhite
        # c = 0
        # for g in self.wGoals:
        #     if g.pawn == Square.pWhite:
        #         c += 1
        # if c == 19:
        #     return Square.pWhite
        elif all(self.board[g.location[0]][g.location[1]].pawn == Square.pBlack for g in self.bGoals):
            return Square.pBlack
        else:
            return None

    def evaluationFunction(self, player):

        def chebyshevDistance(p0, p1):
            dx = abs(p0[0] - p1[0])
            dy = abs(p0[1] - p1[1])
            # Chebyshev constants
            D = 1
            D2 = 1
            return D * (dx + dy) + (D2 - 2 * D) * min(dx, dy)

        def manhattanDistance(p0, p1):
            dx = abs(p0[0] - p1[0])
            dy = abs(p0[1] - p1[1])
            return dx + dy

        value = 0
        distanceHeuristic = manhattanDistance
        for col in range(self.boardSize):
            for row in range(self.boardSize):

                square = self.board[row][col]

                if square.pawn == Square.pWhite:
                    distances = [distanceHeuristic(square.location, g.location) for g in self.wGoals if
                                 g.pawn != Square.pWhite]
                    value -= max(distances) if len(distances) else -50

                elif square.pawn == Square.pBlack:
                    distances = [distanceHeuristic(square.location, g.location) for g in self.bGoals if
                                 g.pawn != Square.pBlack]
                    value += max(distances) if len(distances) else -50

        if player == Square.pBlack:
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
    move = fileInput[0]
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

    h = Halma(16)
    h.updateBoard(currentBoardConfig)

    treeDepthSearch = 3
    maxAvailableTime = time.time() + timeRemaining
    maxAvailableTimeTurn = min(time.time() + 30, maxAvailableTime)
    _, move, prunes, boards = h.minimax(treeDepthSearch, playerTurn, maxAvailableTimeTurn, playerTurn)
    if move:
        # print("Total number of boards/nodes generated : ", boards)
        # print("Moves:", move)
        # print("Total number of nodes pruned :", prunes)
        output = ""
        if (abs(move[0][0] - move[1][0]) == 1 or abs(move[0][1] - move[1][1])) == 1:
            output = "E " + str(move[0][1]) + "," + str(move[0][0]) + " " + str(move[1][1]) + "," + str(move[1][0])
        else:
            output = ""
            pathList = h.getMovePath(h.moveMap[move[0]], move[0], move[1])
            i = 0
            j = 1
            while j != len(pathList):
                output += "J " + str(pathList[i][1]) + "," + str(pathList[i][0]) + " " + str(pathList[j][1]) + "," + str(
                    pathList[j][0]) + "\n"
                i += 1
                j += 1
        with open("output.txt", "w+") as fWrite:
            fWrite.write(output.strip())
        end = time.time()
    else:
        print("Invalid game configuration or player already won")
        end = time.time()

    # Print search result stats
    # print("Time to compute : ", round(end - start, 4))
