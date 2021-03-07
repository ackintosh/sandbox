const THREE = require('three');
const Stats = require('stats-js');

const fontJson = require('./fonts/helvetiker_regular.typeface.json');
const font = new THREE.Font(fontJson);


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
  const scale = 1;
  const camera = new THREE.PerspectiveCamera(
    45,
    width / height,
    1,
    1000 * scale
  );
  camera.position.set(0, 0, +1000);


  // ///////////////////////////////////////
  // 4. 立方体を作る
  //
  // 立方体はメッシュという表示オブジェクトを使用して作成する
  // メッシュを作るには、ジオメトリ（形状）とマテリアル（素材）を用意する必要がある
  // ///////////////////////////////////////

  // *ジオメトリ（形状）を作る*
  // ジオメトリは頂点情報や面情報を持っている
  // 立方体や直方体のような箱状の形状を生成するための `BoxGeometry` を使用する
  // new THREE.BoxGeometry(幅, 高さ, 奥行き)
//  const geometry = new THREE.BoxGeometry(500, 500, 500);

  // *マテリアル（素材）を作る*
  // マテリアルは色や質感の情報を持っている
//  const material = new THREE.MeshStandardMaterial({
//      color: 0x0000ff
//  });

  // ジオメトリとマテリアルを使って、メッシュを作り、シーンに追加する
  // new THREE.Mesh(ジオメトリ,マテリアル)
//  const box = new THREE.Mesh(geometry, material);
  // シーンに追加
//  scene.add(box);


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
  // 6. 描画する
  // ///////////////////////////////////////
  // 下記だと、一度描画するだけなのでアニメーションできない
  // アニメーションさせるには、7. を行う
  // renderer.render(scene, camera);


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
      // create new node
      const depth = 0;
      const pos = {x: 0, y: 0, z: 0};
      const goroutine = {name: 'new node'};

      const x = pos.x;
      const y = pos.y;
      const z = pos.z;

      // create new line
      // https://threejs.org/docs/index.html#manual/en/introduction/Drawing-lines
      const points = [];
      points.push( new THREE.Vector3( x, y, z ) );
      points.push( new THREE.Vector3( x, y + 100, z ) );
      const geometry = new THREE.BufferGeometry().setFromPoints( points );
      const material = new THREE.LineBasicMaterial( { color: 0xffffff } );
		  goroutine.line = new THREE.Line(geometry, material);

		  // create cap text
		  // https://threejs.org/docs/index.html#manual/en/introduction/Creating-text
		  const textGeometry = new THREE.TextGeometry( goroutine.name, {
      		font: font,
      		size: 20,
      		height: 2,
      		curveSegments: 12,
      		bevelEnabled: false,
      		bevelThickness: 10,
      		bevelSize: 8,
      		bevelOffset: 0,
      		bevelSegments: 5
      	} );
      const textMaterial = new THREE.MeshBasicMaterial({color: 0xffffff})
		  const text = new THREE.Mesh( textGeometry, textMaterial );
		  text.position.x = x;
		  text.position.y = y;
		  text.position.z = z;
//		  text.lookAt( _cam_position );

      // add to scene
		  scene.add(text);
		  scene.add(goroutine.line);
    }

    step += 1;

    // 箱を回転させる
//    box.rotation.x += 0.01;
//    box.rotation.y += 0.01;
  }
}

