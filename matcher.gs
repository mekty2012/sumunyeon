function main() {
  matcher(45, 2, 3, 6, 2);
}
function myTest() {
  Logger.log(indexToTime(22.0, 14.0, 45)); // i n OUTPUT
  
}
function matcher(OUTPUT, availableColumn, scheduleColumn, resultColumn, rowStart) {
  Logger.log("matcher");
  // OUTPUT = 45 (총 45번의 면접이 가능함)
  // availableColumn : 합격 여부 정보가 담겨있는 열의 index. (A:1, B:2, ...) 
  // scheduleColumn : 면접 가능 시간 정보가 담겨있는 열의 index. (A:1, B:2, ...)
  // resultColumn : 면접 시간 기록 정보가 작성될 열의 index. (A:1, B:2, ...)
  // rowStart : 각 정보가 시작하는(또는 시작할) 행의 index. (1:1, 2:2, ...)
  var sheet = SpreadsheetApp.getActiveSheet();
  var avaliableList = [];
  var scheduleList = [];
  var i = 0;
  while (true) {
    var available = parseInt(sheet.getRange(rowStart + i, availableColumn).getValue());
    if (available == 1) {
      avaliableList.push(rowStart + i);
      scheduleList.push(sheet.getRange(rowStart + i, scheduleColumn).getValue());
    }
    else if (available != 0) {
      break;
    }
    i++;
  }
  var graph = [];
  var j;
  var n = avaliableList.length;
  for (i=0;i<n + OUTPUT + 2;i++) {
    graph.push([]);
    for (j = 0;j<n + OUTPUT + 2;j++) {
      if (i == 0 && j > 0 && j <= n) {graph[i].push(1);}
      else if (j == 0 && i > 0 && i <= n) {graph[i].push(1);}
      else if (i == n + OUTPUT + 1 && j == n + OUTPUT + 1) {graph[i].push(0);}
      else if (i == n + OUTPUT + 1 && j > n) {graph[i].push(1);}
      else if (j == n + OUTPUT + 1 && i > n) {graph[i].push(1);}
      else {graph[i].push(0);}
    }
  }
  for (i=0;i<n;i++) {
    var schedule = timeTextToArray(scheduleList[i], OUTPUT);
    for (j=0;j<schedule.length;j++) {
      graph[i+1][n+j+1] = schedule[j];
      graph[n+j+1][i+1] = schedule[j];
    }
  }
  
  var matchResult = bipartiteMatching(graph, 0, n + OUTPUT + 1);
  
  for (i=0;i<n;i++) {
    var result = matchResult[i];
    var resultData = -1;
    for (j=0;j<OUTPUT;j++) {
      if (matchResult[n+j+1][i+1] == 2) {
        resultData = n+j+1;
        break;
      }
    }
    Logger.log(resultData);
    sheet.getRange(avaliableList[i], resultColumn).setValue(indexToTime(resultData, n, OUTPUT));
  }
}
function timeTextToArray(text, OUTPUT) {
  // 이거 코틀린이면 세줄에 끝나는데
  var result = [];
  
  var days = text.split(",");
  var i;
  for (i=0;i<days.length;i++) {
    var times = days[i].split("~");
    var start = timeTextToMinute(times[0]);
    var end = timeTextToMinute(times[1]);
    var j;
    for (j = 0;j<OUTPUT / 3;j++) {
      if (1140 + 20 * j >= start && 1160 + 20 * j <= end) {
        result.push(1);
      }
      else {
        result.push(0);
      }
    }
  }
  
  return result;
}
function timeTextToMinute(text) {
  var hourAndMinute = text.split(":");
  return parseInt(hourAndMinute[0]) * 60 + parseInt(hourAndMinute[1]);
}
function indexToTime(i, n, OUTPUT) {
  if (i <= n || i >= n + OUTPUT + 1) {return "Invalid";}
  var dayMap = ["First Day", "Second Day", "Third Day"];
  var timeMap = ["19:00~19:20","19:20~19:40","19:40~20:00","20:00~20:20","20:20~20:40","20:40~21:00","21:00~21:20","21:20~21:40","21:40~22:00","22:00~22:20","22:20~22:40","22:40~23:00","23:00~23:20","23:20~23:40","23:40~24:00"];
  return dayMap[Math.floor((i - n - 1) / (OUTPUT / 3))] + " , " + timeMap[(i - n - 1) % (OUTPUT / 3)];
}
function bipartiteMatching(graph, start, end) {
  Logger.log("bipartiteMatching");
  var result = [];
  var i;
  var j;
  for (i=0;i<graph.length;i++) {
    result.push([]);
    for (j=0;j<graph.length;j++) {
      result[i].push(graph[i][j]);
    }
  }
  while (true) {
    var pathAndFlow = bfs(result, start, end);
    var path = pathAndFlow[0];
    var flow = pathAndFlow[1];
    if (flow <= 0) {break;}
    for (i = 0;i<path.length - 1;i++) {
      result[path[i]][path[i+1]] -= 1;
      result[path[i+1]][path[i]] += 1;
    }
  }
  return result;
}

function bfs(graph, start, end) {
  Logger.log("bfs");
  // graph : Array<Array<Int>> (matrix)
  // start : Int (index)
  // end : Int (index)
  var mark = [];
  var i;
  for (i=0;i<graph.length;i++) {
    mark.push(i == start);
  }
  var queue = [[start, [start], 2]];
  while (queue.length != 0) {
    var tuple = queue.shift();
    var item = tuple[0];
    var path = tuple[1];
    var flow = tuple[2];
    mark[item] = true;
    if (item == end) {
      return [path, flow];
    }
    for (i = 0;i < graph.length;i++) {
      if ((!mark[i]) && graph[item][i] > 0) {
        var newPath = [];
        var j;
        for (j = 0;j < path.length;j++) {
          newPath.push(path[j]);
        }
        newPath.push(i);
        if (flow >= graph[item][i]) {
          queue.push([i, newPath, graph[item][i]]);
        }
        else {
          if (i == end) {
            return [newPath, flow];
          }
          queue.push([i, newPath, flow]);
        }
      }
    }
  }
  return [[], -1];
}
