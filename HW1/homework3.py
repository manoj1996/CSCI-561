"""
Code to navigate the mars rover from landing site to target site in an efficient path
"""
import heapq


def bfs(graph, landingsite, targetsite):
    visitedMatrix = [[0 for col in range(len(graph[0]))] for row in range(len(graph))]
    # Keeps track of the nodes visited in the graph so as to avoid loops

    parentMapping = dict()
    # Maps the node to its parent so that path can be computed for each node from root

    bfsTree = createGraph(graph, algorithm)
    # Tree version of the adjacency matrix

    frontier = list()
    # Keeps hold of the nodes to be visited in a queue order

    frontier.append([0, landingsite[0], landingsite[1]])
    parentMapping[(landingsite[0], landingsite[1])] = None
    # Root(landing side) of the tree points to None

    count = 0
    while frontier:
        count += 1
        node = frontier.pop(0)
        if visitedMatrix[node[1]][node[2]] == 1:  # Already visited
            continue
        visitedMatrix[node[1]][node[2]] = 1
        if node[1] == targetsite[0] and node[2] == targetsite[1]:  # Reached target site
            finalPath = ""
            x, y = node[1], node[2]
            while parentMapping[(x, y)] is not None:
                finalPath = str(y) + "," + str(x) + " " + finalPath
                (x, y) = parentMapping.get((x, y))
            finalPath = str(y) + "," + str(x) + " " + finalPath
            # print("Total Cost:", node[0])
            # print("Solution found after visiting {0} nodes:".format(count))
            return finalPath.strip() + "\n"

        costTillCurrentNode = node[0]
        for adjacent in bfsTree.get((node[1], node[2])):
            if visitedMatrix[adjacent[1]][adjacent[2]] == 0:
                adjacent[0] = adjacent[0] + costTillCurrentNode
                frontier.append(adjacent)
                if (adjacent[1], adjacent[2]) not in parentMapping:
                    parentMapping[(adjacent[1], adjacent[2])] = (node[1], node[2])
    return "FAIL\n"


def ucs(graph, landingsite, targetsite):
    visitedMatrix = [[0 for col in range(len(graph[0]))] for row in range(len(graph))]
    # create a visited array to track the visited nodes

    parentMapping = dict()
    ucsTree = createGraph(graph, algorithm)
    frontier = list()
    frontier.append([0, landingsite[0], landingsite[1]])
    heapq.heapify(frontier)  # Creates a min heap by default
    parentMapping[(landingsite[0], landingsite[1])] = None
    count = 0
    while frontier:
        count += 1
        node = heapq.heappop(frontier)
        if visitedMatrix[node[1]][node[2]] == 1:
            continue
        visitedMatrix[node[1]][node[2]] = 1
        if node[1] == targetsite[0] and node[2] == targetsite[1]:
            finalPath = ""
            x, y = node[1], node[2]
            while parentMapping[(x, y)] is not None:
                finalPath = str(y) + "," + str(x) + " " + finalPath
                (x, y) = parentMapping.get((x, y))
            finalPath = str(y) + "," + str(x) + " " + finalPath
            # print("Total Cost:", node[0])
            # print("Solution found after visiting {0} nodes:".format(count))
            return finalPath.strip() + "\n"
        costTillCurrentNode = node[0]
        for adjacent in ucsTree.get((node[1], node[2])):
            if visitedMatrix[adjacent[1]][adjacent[2]] == 0:
                adjacent[0] = adjacent[0] + costTillCurrentNode
                heapq.heappush(frontier, adjacent)
                if (adjacent[1], adjacent[2]) not in parentMapping:
                    parentMapping[(adjacent[1], adjacent[2])] = (node[1], node[2])
    return "FAIL\n"


def astar(graph, landingsite, targetsite, heuristicMatrix):
    parentMapping = dict()
    visitedMatrix = [[0 for col in range(len(graph[0]))] for row in range(len(graph))]
    # create a visited array to track the visited nodes
    astarTree = createGraph(graph, algorithm)
    frontier = list()
    frontier.append([heuristicMatrix[landingsite[0]][landingsite[1]], 0, landingsite[0], landingsite[1]])
    heapq.heapify(frontier)
    parentMapping[(landingsite[0], landingsite[1])] = None
    count = 0
    while frontier:
        count += 1
        node = heapq.heappop(frontier)
        if visitedMatrix[node[2]][node[3]] == 1:
            continue
        visitedMatrix[node[2]][node[3]] = 1
        if node[2] == targetsite[0] and node[3] == targetsite[1]:
            finalPath = ""
            x, y = node[2], node[3]
            while parentMapping[(x, y)] is not None:
                finalPath = str(y) + "," + str(x) + " " + finalPath
                (x, y) = parentMapping.get((x, y))
            finalPath = str(y) + "," + str(x) + " " + finalPath
            # print("Total Cost:", node[1])
            # print("Solution found after visiting {0} nodes:".format(count))
            return finalPath.strip() + "\n"
        costTillCurrentNode = node[1]
        for adjacent in astarTree.get((node[2], node[3])):
            if visitedMatrix[adjacent[1]][adjacent[2]] == 0:
                if (adjacent[1], adjacent[2]) not in parentMapping:
                    parentMapping[(adjacent[1], adjacent[2])] = (node[2], node[3])
                adjacent[0] = adjacent[0] + costTillCurrentNode + int(
                    abs(graph[node[2]][node[3]] - graph[adjacent[1]][adjacent[2]]))
                heuristicValue = adjacent[0] + heuristicMatrix[adjacent[1]][adjacent[2]]
                adjacent.insert(0, heuristicValue)
                heapq.heappush(frontier, adjacent)
    return "FAIL\n"


def heuristicChebyshev(node1, node2, unitPathCost):
    dx = abs(node1[0]-node2[0])
    dy = abs(node1[1]-node2[1])
    #Chebyshev constants
    D = 1
    D2 = round(2**0.5, 1)
    return int((D * (dx + dy) + (D2 - 2*D) * min(dx, dy))*unitPathCost)


def computeHeuristicMatrix(heuristicMatrix, targetSite):
    for i in range(len(heuristicMatrix)):
        for j in range(len(heuristicMatrix[0])):
            heuristicMatrix[i][j] = heuristicChebyshev((i, j), targetSite, unitPathCost=10)


def createGraph(graph, algorithm):
    mapping = dict()
    for row in range(len(graph)):
        for col in range(len(graph[0])):
            if (row, col) not in mapping:
                mapping[(row, col)] = []
            if algorithm.upper() == "BFS":
                validPos = getValidAdjacentSpaces(graph, [row, col], algorithm)
            elif algorithm.upper() == "UCS" or algorithm.upper() == "A*":
                validPos = getValidAdjacentSpaces(graph, [row, col], algorithm)
            for k in validPos:
                mapping[(row, col)].append(k)
    return mapping


def getValidAdjacentSpaces(graph, currentpos, algorithm):
    pathCostNEWS = 10
    if algorithm.upper() == "UCS" or algorithm.upper() == "A*":
        pathCostDiagonal = 14
    else:
        pathCostDiagonal = 1
        pathCostNEWS = 1
    validPos = list()  # contains the list of valid positions for the next move

    # check north
    if currentpos[0] - 1 >= 0 and abs(
            graph[currentpos[0]][currentpos[1]] - graph[currentpos[0] - 1][currentpos[1]]) <= zMax:
        validPos.append([pathCostNEWS, currentpos[0] - 1, currentpos[1]])
    # check south
    if currentpos[0] + 1 < len(graph) and abs(
            graph[currentpos[0]][currentpos[1]] - graph[currentpos[0] + 1][currentpos[1]]) <= zMax:
        validPos.append([pathCostNEWS, currentpos[0] + 1, currentpos[1]])
    # check west
    if currentpos[1] - 1 >= 0 and abs(
            graph[currentpos[0]][currentpos[1]] - graph[currentpos[0]][currentpos[1] - 1]) <= zMax:
        validPos.append([pathCostNEWS, currentpos[0], currentpos[1] - 1])
    # check east
    if currentpos[1] + 1 < len(graph[0]) and abs(
            graph[currentpos[0]][currentpos[1]] - graph[currentpos[0]][currentpos[1] + 1]) <= zMax:
        validPos.append([pathCostNEWS, currentpos[0], currentpos[1] + 1])
    # check northwest
    if currentpos[0] - 1 >= 0 and currentpos[1] - 1 >= 0 and abs(
            graph[currentpos[0]][currentpos[1]] - graph[currentpos[0] - 1][currentpos[1] - 1]) <= zMax:
        validPos.append([pathCostDiagonal, currentpos[0] - 1, currentpos[1] - 1])
    # check northEast
    if currentpos[0] - 1 >= 0 and currentpos[1] + 1 < len(graph[0]) and abs(
            graph[currentpos[0]][currentpos[1]] - graph[currentpos[0] - 1][currentpos[1] + 1]) <= zMax:
        validPos.append([pathCostDiagonal, currentpos[0] - 1, currentpos[1] + 1])
    # check southWest
    if currentpos[0] + 1 < len(graph) and currentpos[1] - 1 >= 0 and abs(
            graph[currentpos[0]][currentpos[1]] - graph[currentpos[0] + 1][currentpos[1] - 1]) <= zMax:
        validPos.append([pathCostDiagonal, currentpos[0] + 1, currentpos[1] - 1])
    # check southEast
    if currentpos[0] + 1 < len(graph) and currentpos[1] + 1 < len(graph[0]) and abs(
            graph[currentpos[0]][currentpos[1]] - graph[currentpos[0] + 1][currentpos[1] + 1]) <= zMax:
        validPos.append([pathCostDiagonal, currentpos[0] + 1, currentpos[1] + 1])
    return validPos


if __name__ == "__main__":
    fileInput = list()
    with open("input401.txt", "r") as f:
        for record in f.readlines():
            fileInput.append(record.strip())
        f.close()

    algorithm = fileInput[0]
    numOfCols, numOfRows = list(map(int, fileInput[1].split(" ")))
    yLanding, xLanding = list(map(int, fileInput[2].split(" ")))
    zMax = int(fileInput[3])
    numOfTargets = int(fileInput[4])

    targetSites = list()

    for i in range(5, 5 + numOfTargets):
        targetSiteY = int(fileInput[i].split(' ')[0])
        targetSiteX = int(fileInput[i].split(' ')[1])
        targetSites.append((targetSiteX, targetSiteY))

    targetSites = list(targetSites)
    adjGraph = list()

    for i in range(5 + numOfTargets, 5 + numOfTargets + numOfRows):
        adjRow = " ".join(fileInput[i].strip().split())
        adjGraph.append(list(map(int, adjRow.split(' '))))

    adjGraph = list(adjGraph)
    fileWrite = ""
    for target in targetSites:
        if algorithm == "BFS":
            fileWrite += bfs(adjGraph, (xLanding, yLanding), target)
        elif algorithm == "UCS":
            fileWrite += ucs(adjGraph, (xLanding, yLanding), target)
        elif algorithm == "A*":
            heuristicMatrix = [[0 for col in range(len(adjGraph[0]))] for row in range(len(adjGraph))]
            computeHeuristicMatrix(heuristicMatrix, target)
            fileWrite += astar(adjGraph, (xLanding, yLanding), target, heuristicMatrix)

    with open("output.txt", "w+") as fout:
        fout.write(fileWrite)
        fout.close()
