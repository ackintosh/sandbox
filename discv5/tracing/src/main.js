import { TrackballControls } from 'three/examples/jsm/controls/TrackballControls';
import { Reader } from "protobufjs";

class Logs {
  constructor() {
    this.logs = new Map();
  }

  add(log) {
    const t = `${log.timestamp.seconds}${log.timestamp.nanos}`;

    if (this.logs.has(t)) {
      const elements = this.logs.get(t);
      elements.push(log);
      this.logs.set(t, elements);
    } else {
      this.logs.set(t, [log]);
    }
  }

  sort() {
    const sorted = [...this.logs].sort(([k, _v], [k2, _v2]) => {
      if (k > k2) {
        return 1;
      } else {
        return -1;
      }
    });

    this.logs = new Map(sorted);
  }

  first() {
      return this.logs.entries().next();
  }
}

class Node {
  constructor(id) {
    this.id = id;
    this.pos = this.calculatePos();

    this.showLine();
    this.showNodeId();
  }

  calculatePos() {
    const angle = 360 / _nodeIds.length * _nodes.length;
    const x = Math.cos(angle * Math.PI / 180) * _distance;
    const z = Math.sin(angle * Math.PI / 180) * _distance;

    return {x: x, y: 0, z: z};
  }

  // create new line
  // https://threejs.org/docs/index.html#manual/en/introduction/Drawing-lines
  showLine() {
    const MAX_POINTS = 500;

    // geometry
    const geometry = new THREE.BufferGeometry();

    // attributes
    const positions = new Float32Array( MAX_POINTS * 3 ); // 3 vertices per point

    let y, yIndex, xIndex, zIndex;
    y = yIndex = xIndex = zIndex = 0;
    for (var i = 0; i < MAX_POINTS; i ++) {
      xIndex = (i * 3);
      yIndex = (i * 3) + 1;
      zIndex = (i * 3) + 2;
      positions[xIndex] = this.pos.x;
      positions[yIndex] = y;
      positions[zIndex] = this.pos.z;
      y = (-1 * _scale) * i;
    }

    geometry.setAttribute( 'position', new THREE.BufferAttribute( positions, 3 ) );

    // draw range
    const drawCount = 2; // draw the first 2 points, only
    geometry.setDrawRange( 0, drawCount );

    // create a blue LineBasicMaterial
    const material = new THREE.LineBasicMaterial( { color: 0xff0000 } );

    this.line = new THREE.Line( geometry, material );
    _scene.add(this.line);
  }

  showNodeId() {
	  const id = createCapText(this.id, this.pos.x, this.pos.y, this.pos.z);
    _scene.add(id);
  }

  sendRandomMessage(toNode, step) {
    const arrow = createArrow(this, toNode, step, COLOR_RANDOM);
    _scene.add(arrow);

    const x = this.pos.x;
    const y = this.line.geometry.getAttribute('position').getY(step);
    const z = this.pos.z;
	  const text = createCapText('Random Message', x, y, z, COLOR_RANDOM);
    _scene.add(text);
  }

  sendMessage(toNode, step, message) {
    const arrow = createArrow(this, toNode, step, message.color());
    _scene.add(arrow);

    const x = this.pos.x;
    const y = this.line.geometry.getAttribute('position').getY(step);
    const z = this.pos.z;
	  const text = createCapText(`Message<${message.name()}>\n${message.capText()}`, x, y, z, message.color());
    _scene.add(text);
  }

  sendWhoAreYou(toNode, step, idNonce, enrSeq) {
    const arrow = createArrow(this, toNode, step, COLOR_WHOAREYOU);
    _scene.add(arrow);

    const x = this.pos.x;
    const y = this.line.geometry.getAttribute('position').getY(step);
    const z = this.pos.z;
	  const text = createCapText(`WHOAREYOU :\n  ${idNonce}\n  ${enrSeq}`, x, y, z, COLOR_WHOAREYOU);
    _scene.add(text);
  }

  sendHandshakeMessage(toNode, step, message) {
    const arrow = createArrow(this, toNode, step, message.color());
    _scene.add(arrow);

    const x = this.pos.x;
    const y = this.line.geometry.getAttribute('position').getY(step);
    const z = this.pos.z;
	  const text = createCapText(`Handshake Message<${message.name()}>\n${message.capText()}`, x, y, z, message.color());
    _scene.add(text);
  }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#ping-request-0x01
class Ping {
  constructor(requestId, enrSeq) {
    this.requestId = requestId;
    this.enrSeq = enrSeq;
  }

  name() {
    return 'PING';
  }

  color() {
    return COLOR_PING;
  }

  capText() {
    return `  ${this.requestId}\n  ${this.enrSeq}`;
  }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#pong-response-0x02
class Pong {
  constructor(requestId, enrSeq, recipientIp, recipientPort) {
    this.requestId = requestId;
    this.enrSeq = enrSeq;
    this.recipientIp = recipientIp;
    this.recipientPort = recipientPort;
  }

  name() {
    return 'PONG';
  }

  color() {
    return COLOR_PONG;
  }

  capText() {
    return `  ${this.requestId}\n  ${this.enrSeq}\n  ${this.recipientIp}\n  ${this.recipientPort}`;
  }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#findnode-request-0x03
class Findnode {
  constructor(requestId, distances) {
    this.requestId = requestId;
    this.distances = distances;
  }

  name() {
    return 'FINDNODE';
  }

  color() {
    return COLOR_FINDNODE;
  }

  capText() {
    return `  ${this.requestId}\n  [${this.distances.join(', ')}]`;
  }
}

// https://github.com/ethereum/devp2p/blob/master/discv5/discv5-wire.md#nodes-response-0x04
class Nodes {
  constructor(requestId, nodes) {
    this.requestId = requestId;
    this.nodes = nodes;
  }

  name() {
    return 'NODES';
  }

  color() {
    return COLOR_NODES;
  }

  capText() {
    return `  ${this.requestId}\n  [${this.nodes.join(', ')}]`;
  }
}

function init() {
  console.log("init --------------------->");
  console.dir(_nodeIds);
  const width = window.innerWidth;
  const height = window.innerHeight;


  // ///////////////////////////////////////
  // Stats
  // https://github.com/mrdoob/stats.js
  // ///////////////////////////////////////
  const stats = new Stats();
  stats.showPanel(0); // 0: fps, 1: ms, 2: mb, 3+: custom
  stats.domElement.style.position = 'absolute';
  stats.domElement.style.left = '8px';
  stats.domElement.style.top = '8px';
  document.body.appendChild(stats.dom);

  // ///////////////////////////////////////
  // Renderer
  // ///////////////////////////////////////
  const renderer = new THREE.WebGLRenderer({
    canvas: document.querySelector("#tracing")
  });

  // デフォルトではレンダラーのサイズが小さいため、setSize()メソッドでサイズを設定
  renderer.setSize(width, height);

  // スマホでも綺麗に見えるように、デバイスピクセル比も設定
  // これを設定しないとスマホだとぼやけてしまう
  renderer.setPixelRatio(window.devicePixelRatio);

  // ///////////////////////////////////////
  // Camera
  //
  // Three.jsではカメラを作成し、その視点から見えるものがレンダラーを介してcanvasへ描画される
  // https://ics.media/entry/14771/images/concept.png
  // ///////////////////////////////////////
  // new THREE.PerspectiveCamera(画角, アスペクト比, 描画開始距離, 描画終了距離)
  const camera = new THREE.PerspectiveCamera(
    45,
    width / height,
    1,
    5000 * _scale
  );
  camera.position.set(0, 0, 2000);

  // TrackballControls
  // https://threejs.org/docs/#examples/en/controls/TrackballControls
  const controls = new TrackballControls(camera, renderer.domElement);

  // ///////////////////////////////////////
  // 5. ライトを作る
  // ///////////////////////////////////////
  // このままでは真っ暗なのでライトを作成する
  // DirectionalLight: 平行光源を意味します。平行光源は太陽光のように一定方向から差し込む光。
  // new THREE.DirectionalLight(色)
  const light = new THREE.DirectionalLight(0xffffff);
  light.intensity = 2; // 光の強さを倍に
  //  光源が斜めから差し込むようにライトの位置を変更しておく
  light.position.set(1, 1, 1);
  // ライトもシーンに追加することで反映される
  _scene.add(light);

  // ///////////////////////////////////////
  // Node
  // ///////////////////////////////////////
  for (let i = 0; i < _nodeIds.length; i++) {
    const node = new Node(_nodeIds[i]);
    _nodes.push(node);
    console.info("Node: " + node.id);
  }

  // ///////////////////////////////////////
  // animate
  // ///////////////////////////////////////
  let step = 0;

  animate();

  function animate() {
    requestAnimationFrame(animate);
    advanceTrace();

    controls.update();
    stats.begin();
    renderer.render(_scene, camera);
    stats.end();
  }

  function advanceTrace() {
    if (step >= MAX_STEPS) {
      return;
    }

    growExistingNodes(step);

    // TODO
    if (step == 4) {
      const fromNode = _nodes[0];
      const toNode = _nodes[1];
      fromNode.sendRandomMessage(toNode, step);
    } else if (step == 5) {
      const fromNode = _nodes[1];
      const toNode = _nodes[0];
      fromNode.sendWhoAreYou(toNode, step, "dummy-id-nonce", "dummy-enr-seq");
    } else if (step == 6) {
      const fromNode = _nodes[0];
      const toNode = _nodes[1];
      const findNode = new Findnode("*** dummy-request-id ***", [255, 254, 253]);
      fromNode.sendHandshakeMessage(toNode, step, findNode);
    } else if (step == 7) {
      const fromNode = _nodes[1];
      const toNode = _nodes[0];
      const nodes = new Nodes("*** dummy-request-id ***", ["dummy-enr1", "dummy-enr2"]);
      fromNode.sendMessage(toNode, step, nodes);
    } else if (step == 8) {
      const fromNode = _nodes[0];
      const toNode = _nodes[1];
      const ping = new Ping("*** dummy-request-id ***", "dummy-enr-seq");
      fromNode.sendMessage(toNode, step, ping);
    } else if (step == 9) {
      const fromNode = _nodes[1];
      const toNode = _nodes[0];
      const pong = new Pong(
        "*** dummy-request-id ***",
        "dummy-enr-seq",
        "dummy-recipient-ip",
        "dummy-recipient-port"
      );
      fromNode.sendMessage(toNode, step, pong);
    }

    step += 1;
  }

  // grow existing nodes along the time axis
  // https://threejs.org/docs/#manual/en/introduction/How-to-update-things
  function growExistingNodes(step) {
    for (let i = 0; i < _nodes.length; i++) {
			const line = _nodes[i].line;
      line.geometry.setDrawRange(0, step);
      line.geometry.attributes.position.needsUpdate = true; // required after the first render
    }
  }
}

// create cap text
// https://threejs.org/docs/index.html#manual/en/introduction/Creating-text
function createCapText(text, x, y, z, color) {
  const textGeometry = new THREE.TextGeometry( text, {
    font: _font,
    size: 20,
    height: 2,
    curveSegments: 12,
    bevelEnabled: false,
    bevelThickness: 10,
    bevelSize: 8,
    bevelOffset: 0,
    bevelSegments: 5
  });

  const textMaterial = new THREE.MeshBasicMaterial({color: color})
  const textMesh = new THREE.Mesh( textGeometry, textMaterial );

  textMesh.position.x = x;
  textMesh.position.y = y;
  textMesh.position.z = z;

  return textMesh;
}

function createArrow(fromNode, toNode, step, color) {
  const targetV = new THREE.Vector3(
    toNode.pos.x,
    toNode.line.geometry.getAttribute('position').getY(step),
    toNode.pos.z
  );
  const head = {
    x: fromNode.pos.x,
    y: fromNode.line.geometry.getAttribute('position').getY(step),
    z: fromNode.pos.z
  };
  const direction = new THREE.Vector3().subVectors(targetV, head);

  // https://threejs.org/docs/index.html#api/en/helpers/ArrowHelper
  return new THREE.ArrowHelper(
    direction.clone().normalize(),
    head,
    direction.length(),
    color,
    10,
    10
  );
}

const _scene = new THREE.Scene();
const Stats = require('stats-js');
const protobuf = require('protobufjs');
const _logs = new Logs();
const _nodes = [];
const _font = new THREE.Font(require('three/examples/fonts/helvetiker_regular.typeface.json'));
const _scale = 100;
const _distance = 500;
const _nodeIds = [];

// TODO: 調整
const MAX_STEPS = 50;

// TODO: 色の調整
const COLOR_RANDOM = 0xffdd00;
const COLOR_WHOAREYOU = 0x00dd00;
const COLOR_PING = 0x0000ff;
const COLOR_PONG = 0xff00ff;
const COLOR_FINDNODE = 0x00d6dd;
const COLOR_NODES = 0xddd600;

// protocol-buffers
// https://developers.google.com/protocol-buffers/docs/reference/javascript-generated
// > deserializeBinary

// protobuf.js
// http://protobufjs.github.io/protobuf.js/Type.html#decodeDelimited

(function () {
  const b = document.getElementById('b');
  b.addEventListener('click', async () => {
    // https://developer.mozilla.org/en-US/docs/Web/API/Window/showOpenFilePicker
    // https://wicg.github.io/file-system-access/#api-showopenfilepicker
    const [handle] = await window.showOpenFilePicker({
      multiple: false,
      types: [
        {
          description: 'trace file',
          accept: {
            'text/plain': ['.log']
          },
        }
      ]
    });

    b.style.display = 'none';

    const file = await handle.getFile();
    // console.dir(file);

    const ab = await file.arrayBuffer();
    // console.dir(ab);
    const bytes = new Uint8Array(ab);
    // console.dir(bytes);

    const reader = Reader.create(bytes);
    // console.dir(reader);

    const root = await protobuf.load('tracing.proto');
    const Log = root.lookupType('tracing.Log');

    const reason = Log.verify(bytes);
    if (reason != null) {
      console.log(reason);
      alert(reason);
      return;
    }

    try {
      while (true) {
        const log = Log.decodeDelimited(reader);
        _logs.add(log);

        if (log.event === 'nodeStarted') {
          _nodeIds.push(log.nodeStarted.nodeId);
          console.dir(log.nodeStarted);
        }
        console.dir(log);
        console.dir(log.event);
      }
    } catch (e) {
      if (e instanceof RangeError) {
        console.log("decoding has done");
      } else {
        throw e;
      }
    }

    _logs.sort();

    init();
  });
})();

// ****************
// test
// ****************
// (async () => {
//   const root = await protobuf.load('person.proto');
//   const Person = root.lookupType('person.Person');
//   const payload = {name: "aaaaaaaa"};
//   console.dir(root);
//   console.dir(Person);
//   console.dir(Person.verify(payload));
//   const msg = Person.create(payload);
//   console.dir(msg);
// })();
