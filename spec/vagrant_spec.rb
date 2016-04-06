require 'spec_helper'

describe 'infrastructure::vagrant' do
  let(:hostname) { 'the-hostname' }
  let(:project_root) { 'the-project-root' }

  let(:chef_run) do
    ChefSpec::SoloRunner.new do |node|
      node.automatic['hostname'] = hostname
      node.set['infrastructure']['project_root'] = project_root
    end.converge(described_recipe)
  end

  it 'includes apt' do
    expect(chef_run).to include_recipe('apt')
  end

  it 'adds the git apt repository' do
    code_name = chef_run.node['lsb']['codename']
    expect(chef_run).to add_apt_repository('git-ppa').with(
      uri: 'http://ppa.launchpad.net/git-core/ppa/ubuntu',
      distribution: code_name,
      components: %w(main),
      key: 'E1DF1F24',
      keyserver: 'keyserver.ubuntu.com')
  end

  %w(
    bash-completion
    curl
    dstat
    git
    iftop
    iotop
    iperf
    jq
    lsof
    man-db
    mlocate
    nano
    strace
    sysstat
    unzip
    wget
    zip
  ).each do |package|
    it "installs #{package}" do
      expect(chef_run).to install_package(package)
    end
  end

  it 'creates ./Vagrantfile' do
    expect(chef_run).to create_template("#{project_root}/Vagrantfile").with(
      source: 'vagrant/Vagrantfile.erb',
      variables: { name: hostname })
  end

  it 'creates ./version if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/version").and_return(false)
    expect(chef_run).to create_template("#{project_root}/version").with(
      source: 'vagrant/version.erb')
  end

  it "doesn't create ./version if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/version").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/version")
  end

  it 'creates ./README.md if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/README.md").and_return(false)
    expect(chef_run).to create_template("#{project_root}/README.md").with(
      source: 'vagrant/README.md.erb',
      variables: { name: hostname })
  end

  it "doesn't create ./README.md if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/README.md").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/README.md")
  end

  it 'creates ./.gemspec if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/.gemspec").and_return(false)
    expect(chef_run).to create_template("#{project_root}/.gemspec").with(
      source: 'vagrant/.gemspec.erb',
      variables: { name: hostname })
  end

  it "doesn't create ./.gemspec if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/.gemspec").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/.gemspec")
  end

  it 'creates ./Gemfile if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/Gemfile").and_return(false)
    expect(chef_run).to create_template("#{project_root}/Gemfile").with(
      source: 'vagrant/Gemfile.erb')
  end

  it "doesn't create ./Gemfile if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/Gemfile").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/Gemfile")
  end

  it 'creates ./Berksfile if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/Berksfile").and_return(false)
    expect(chef_run).to create_template("#{project_root}/Berksfile").with(
      source: 'vagrant/Berksfile.erb')
  end

  it "doesn't create ./Berksfile if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/Berksfile").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/Berksfile")
  end

  it 'creates ./Rakefile' do
    expect(chef_run).to create_template("#{project_root}/Rakefile").with(
      source: 'vagrant/Rakefile.erb')
  end

  it 'creates ./metadata.rb if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/metadata.rb").and_return(false)
    expect(chef_run).to create_template("#{project_root}/metadata.rb").with(
      source: 'vagrant/metadata.rb.erb',
      variables: { name: hostname })
  end

  it "doesn't create ./metadata.rb if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/metadata.rb").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/metadata.rb")
  end

  it 'creates ./chefignore if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/chefignore").and_return(false)
    expect(chef_run).to create_template("#{project_root}/chefignore").with(
      source: 'vagrant/chefignore.erb')
  end

  it "doesn't create ./chefignore if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/chefignore").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/chefignore")
  end

  it 'creates ./.gitignore if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/.gitignore").and_return(false)
    expect(chef_run).to create_template("#{project_root}/.gitignore").with(
      source: 'vagrant/.gitignore.erb')
  end

  it "doesn't create ./.gitignore if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/.gitignore").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/.gitignore")
  end

  it 'creates ./.rspec' do
    expect(chef_run).to create_file("#{project_root}/.rspec").with(
      content: "--color --format documentation\n")
  end

  it 'creates ./.rubocop.yml' do
    expect(chef_run).to create_template("#{project_root}/.rubocop.yml").with(
      source: 'vagrant/.rubocop.yml.erb')
  end

  it 'creates ./.editorconfig' do
    expect(chef_run).to create_template("#{project_root}/.editorconfig").with(
      source: 'vagrant/.editorconfig.erb')
  end

  it 'creates ./.sublime-project if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?)
      .with("#{project_root}/.sublime-project").and_return(false)
    expect(chef_run).to create_template("#{project_root}/.sublime-project").with(
      source: 'vagrant/.sublime-project.erb')
  end

  it "doesn't create ./.sublime-project if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?)
      .with("#{project_root}/.sublime-project").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/.sublime-project")
  end

  it 'creates ./recipes' do
    expect(chef_run).to create_directory("#{project_root}/recipes").with(
      owner: 'vagrant',
      group: 'vagrant')
  end

  it 'creates ./recipes/vagrant.rb if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?)
      .with("#{project_root}/recipes/vagrant.rb").and_return(false)
    expect(chef_run).to create_template("#{project_root}/recipes/vagrant.rb").with(
      source: 'vagrant/recipes/vagrant.rb.erb')
  end

  it "doesn't create ./recipes/vagrant.rb if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?)
      .with("#{project_root}/recipes/vagrant.rb").and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/recipes/vagrant.rb")
  end

  it 'creates ./spec' do
    expect(chef_run).to create_directory("#{project_root}/spec").with(
      owner: 'vagrant',
      group: 'vagrant')
  end

  it 'creates ./spec/vagrant_spec.rb if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/spec/vagrant_spec.rb")
      .and_return(false)
    expect(chef_run).to create_template("#{project_root}/spec/vagrant_spec.rb").with(
      source: 'vagrant/spec/vagrant_spec.rb.erb',
      variables: { name: hostname })
  end

  it "doesn't create ./spec/vagrant_spec.rb if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/spec/vagrant_spec.rb")
      .and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/spec/vagrant_spec.rb")
  end

  it 'creates ./spec/spec_helper.rb if it is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/spec/spec_helper.rb")
      .and_return(false)
    expect(chef_run).to create_template("#{project_root}/spec/spec_helper.rb").with(
      source: 'vagrant/spec/spec_helper.rb.erb')
  end

  it "doesn't create ./spec/spec_helper.rb if it exists" do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/spec/spec_helper.rb")
      .and_return(true)
    expect(chef_run).to_not create_template("#{project_root}/spec/spec_helper.rb")
  end

  it 'forces color shell prompts' do
    expect(chef_run).to run_execute(
      "sed -i 's|#force_color|force_color|' /home/vagrant/.bashrc")
  end

  it 'creates a softlink to the project root named after the project' do
    expect(chef_run).to create_link("/home/vagrant/#{hostname}")
      .with(to: project_root)
  end

  describe 'when the softlink would lead to itself' do
    let(:project_root) { "/home/vagrant/#{hostname}" }

    it "doesn't creates the softlink" do
      expect(chef_run).to_not create_link("/home/vagrant/#{hostname}")
    end
  end

  it 'creates /home/vagrant/.irbrc' do
    expect(chef_run).to create_template('/home/vagrant/.irbrc').with(
      source: 'home/vagrant/.irbrc.erb')
  end

  it 'initializes chefdk for bash with a /etc/profile.d entry' do
    expect(chef_run).to create_template('/etc/profile.d/chefdk.sh').with(
      source: 'etc/profile.d/chefdk.sh.erb')
  end

  it 'installs bundler dependencies if Gemfile exists' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/Gemfile").and_return(true)
    expect(chef_run).to run_execute('bundle-install').with(
      command: "bundle install --gemfile=#{project_root}/Gemfile",
      user: 'vagrant')
  end

  it 'does not install bundler dependencies if Gemfile is absent' do
    allow(File).to receive(:exist?).and_call_original
    allow(File).to receive(:exist?).with("#{project_root}/Gemfile").and_return(false)
    expect(chef_run).to_not run_execute('bundle-install')
  end

  it 'runs the project spec' do
    cookbook_path =
      chef_run.run_context.cookbook_collection['infrastructure'].root_paths.first
    expect(chef_run).to run_execute('rspec-project-spec').with(
      command: "rspec --format documentation #{cookbook_path}/spec/project_spec.rb",
      cwd: project_root)
  end
end
