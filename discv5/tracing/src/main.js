import { OrbitControls } from 'three/examples/jsm/controls/OrbitControls';

const _scene = new THREE.Scene();
const Stats = require('stats-js');
const _nodes = [];
const _font = new THREE.Font(require('three/examples/fonts/helvetiker_regular.typeface.json'));
const _scale = 1;
const _speed = 1; // 1/x time multiplier
const _distance = 500;
const _totalNodeCount = 3;

class Node {
  constructor(name) {
    this.name = name;
    this.pos = this.calculatePos();

    this.showLine();
    this.showName();
  }

  calculatePos() {
    const angle = 360 / _totalNodeCount * _nodes.length;
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
      y += -1 * i;
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

  // create cap text
  // https://threejs.org/docs/index.html#manual/en/introduction/Creating-text
  showName() {
	  const name = createCapText(this.name, this.pos.x, this.pos.y, this.pos.z);
    _scene.add(name);
  }

  // https://threejs.org/docs/index.html#api/en/helpers/ArrowHelper
  sendFindNode(toNode, step) {
    const targetV = new THREE.Vector3(
      toNode.pos.x,
      toNode.line.geometry.getAttribute('position').getY(step),
      toNode.pos.z
    );
    const head = {
      x: this.pos.x,
      y: this.line.geometry.getAttribute('position').getY(step),
      z: this.pos.z
    };
    const direction = new THREE.Vector3().subVectors(targetV, head);

    const arrow = new THREE.ArrowHelper(
      direction.clone().normalize(),
      head,
      direction.length(),
      0x00d6dd,
      10,
      10
    );
    _scene.add( arrow );

//	  return createCapText(this.name, this.pos.x, this.pos.y, this.pos.z);
  }
}

window.addEventListener('DOMContentLoaded', init);

//	var _colors3 = {
//        "send_arrow":  "#00D6DD",
//        "send_value":  "#00D6DD",
//        "go_normal":  "#D4FF00",
//        "go_link":  "#B1B4B5",
//        "go_blocked":  "#ED0000",
//        "go_sleep":  "#6C8200",
//        "go_cap":  "#D4FF00",
//    };
//
//	var _colors = _colors3;
//
//const _mats = {
//	"go_normal": new THREE.LineBasicMaterial( { color: _colors["go_normal"], linewidth: 5 } ),
//	"go_sleep": new THREE.LineBasicMaterial( { color: _colors["go_sleep"], linewidth: 2 } ),
//	"go_blocked": new THREE.LineBasicMaterial( { color: _colors["go_blocked"], linewidth: 2 } ),
//	"go_link": new THREE.LineBasicMaterial( { color: _colors["go_link"], linewidth: 1, } ),
//	"go_cap": new THREE.MeshBasicMaterial({color: _colors["go_cap"]}),
//	"send_value": new THREE.MeshBasicMaterial({color: _colors["send_value"]}),
//	"send_arrow": new THREE.LineBasicMaterial({color: _colors["send_arrow"]}),
//	"channel": new THREE.MeshBasicMaterial( {color: _colors["channel"]} ),
//};

function init() {
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
  camera.position.set(0, 0, +1000);

  // OrbitControls
  // https://threejs.org/docs/index.html#examples/en/controls/OrbitControls
  const controls = new OrbitControls(camera, renderer.domElement);

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
  // animate
  // ///////////////////////////////////////
  var step = 0;
  tick();

  function tick() {
    requestAnimationFrame(tick);
    advanceTrace();

    controls.update();
    stats.begin();
    renderer.render(_scene, camera);
    stats.end();
  }

  function advanceTrace() {
    if (step < _totalNodeCount) { // FIXME
      const node = new Node('node #' + step);
		  _nodes.push(node);
		  console.info("Added a node: " + node.name);
    }

    growExistingNodes(step);

    if (step == 20) { // FIXME
      const fromNode = _nodes[0];
      const toNode = _nodes[1];
      fromNode.sendFindNode(toNode, step);
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

function createCapText(text, x, y, z) {
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

  const textMaterial = new THREE.MeshBasicMaterial({color: 0xffffff})
  const textMesh = new THREE.Mesh( textGeometry, textMaterial );

  textMesh.position.x = x;
  textMesh.position.y = y;
  textMesh.position.z = z;

  return textMesh;
}
