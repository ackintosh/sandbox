//const THREE = require('three');

//const OrbitControls = require('@three/OrbitControls');
//import OrbitControls from 'three/examples/js/controls/OrbitControls.js';
//const f = require('three/examples/js/controls/OrbitControls.js');

//import { OrbitControls } from 'three/examples/jsm/controls/OrbitControls';


//import 'OrbitControls';

const Stats = require('stats-js');

const _font = new THREE.Font(require('three/examples/fonts/helvetiker_regular.typeface.json'));
const _scale = 1;
const _speed = 1; // 1/x time multiplier

class Node {
  constructor(name, pos) {
    this.name = name;
    this.pos = pos;
    this.line = this.createLine();
  }

  // create new line
  // https://threejs.org/docs/index.html#manual/en/introduction/Drawing-lines
  createLine() {
    const MAX_POINTS = 500;

    // geometry
    const geometry = new THREE.BufferGeometry();

    // attributes
    const positions = new Float32Array( MAX_POINTS * 3 ); // 3 vertices per point

    let y, yIndex;
    y = yIndex = 0;
    for (var i = 0; i < MAX_POINTS; i ++) {
      yIndex = (i * 3) + 1;
      positions[yIndex] = y;
      y += -1 * i;
    }

    geometry.setAttribute( 'position', new THREE.BufferAttribute( positions, 3 ) );

    // draw range
    const drawCount = 2; // draw the first 2 points, only
    geometry.setDrawRange( 0, drawCount );

    //create a blue LineBasicMaterial
    const material = new THREE.LineBasicMaterial( { color: 0xff0000 } );

    return new THREE.Line( geometry, material );
  }

  // create cap text
  // https://threejs.org/docs/index.html#manual/en/introduction/Creating-text
  createNameGeometry() {
	  const textGeometry = new THREE.TextGeometry( this.name, {
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
	  const text = new THREE.Mesh( textGeometry, textMaterial );
	  text.position.x = this.pos.x;
	  text.position.y = this.pos.y;
	  text.position.z = this.pos.z;

	  return text;
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
  const nodes = [];
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
  // Scene
  //
  // シーン: オブジェクトや光源などの置き場
  // ///////////////////////////////////////
  const scene = new THREE.Scene();


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
    1000 * _scale
  );
  camera.position.set(0, 0, +1000);


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
  scene.add(light);


  // ///////////////////////////////////////
  // animate
  // ///////////////////////////////////////
  var step = 0;
  tick();

  function tick() {
    requestAnimationFrame(tick);
    advanceTrace();

    stats.begin();
    renderer.render(scene, camera);
    stats.end();
  }

  function advanceTrace() {
    if (step == 0) {
      const node = newNode('new node');

      // add to scene
		  scene.add(node.createNameGeometry());
		  scene.add(node.line);

		  nodes.push(node);
		  console.info("Added a node: " + node.name);
    }

    growExistingNodes(step);

    step += 1;
  }

  // grow existing nodes along the time axis
  // https://threejs.org/docs/#manual/en/introduction/How-to-update-things
  function growExistingNodes(step) {
    for (node of nodes) {
			const line = node.line;
      line.geometry.setDrawRange(0, step);
      line.geometry.attributes.position.needsUpdate = true; // required after the first render
    }
  }
}

function newNode(name) {
  return new Node(name, {x: 0, y: 0, z: 0});
}
